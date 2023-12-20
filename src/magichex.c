#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>

typedef struct var Var;

/* constraint variable; if lo==hi, this is the variable's value */
typedef struct var {
#ifndef NDEBUG
  long id; /* variable id; id<0 if the variable is not part of the hexagon */
#endif
  long lo; /* lower bound */
  long hi; /* upper bound */
} Var;

typedef struct Hexagon {
  Var *vs;
  unsigned char *usageMatrix;
} Hexagon;

/* representation of a hexagon of order n: (2n-1)^2 square array
   for a hexagon of order 2:
     A B
    C D E
     F G
   the representation is:
    A B .
    C D E
    . F G
   The . slots have lo>hi.

   The variable array is organized as a single-dimension array with accesses
   vs[y*r+x]
   This allows to access the diagonal with stride 2*order

   Variable names n, r, H, S according to German Wikipedia Article
   Instead of "i", the deviation variable is called "d" (d=0 means
   that the sum=0; to have the lowest value 1, d=2)
   
   n is the order (number of elements of a side of the hexagon).
   r = 2n-1 (length of the middle row/diagonals)
   H = 3n^2-3n+1 (number of variables)
   M = dH (sum of each row/diagonal)
   lowest  value = dr - (H-1)/2
   highest value = dr + (H-1)/2
*/

#define NO_SOLUTION (0)
#define DID_CHANGE  (1)
#define NO_CHANGE   (2)

unsigned long solutions = 0; /* counter of solutions */
unsigned long leafs = 0; /* counter of leaf nodes visited in the search tree */

static long min(long a, long b)
{
  return (a<b)?a:b;
}

static long max(long a, long b)
{
  return (a>b)?a:b;
}


/* unless otherwise noted, the following functions return

   0 if there is no solution (i.e., the action eliminates all values
   from a variable),

   1 if there was a change 

   2 if there was no change 
*/


static int sethi(Var *v, long x) {
  assert(v->id >= 0);
  if (x < v->hi) {
    v->hi = x;
    if (v->lo <= v->hi)
      return DID_CHANGE;
    else
      return NO_SOLUTION;
  }
  return NO_CHANGE;
}

static int setlo(Var *v, long x) {
  assert(v->id >= 0);
  if (x > v->lo) {
    v->lo = x;
    if (v->lo <= v->hi)
      return DID_CHANGE;
    else
      return NO_SOLUTION;
  }
  return NO_CHANGE;
}

/* returns 0 if there is no solution, 1 if one of the variables has changed */
static int lessthan(Var *v1, Var *v2)
{
  assert(v1->id >= 0);
  assert(v2->id >= 0);
  int f = sethi(v1, v2->hi-1);
  if (f != NO_CHANGE)
    return f;
  return (setlo(v2, v1->lo+1));
}
    
/* reduce the ranges of the variables as much as possible (with the
   constraints we use);  returns 1 if all variables still have a
   non-empty range left, 0 if one has an empty range */
static int solve(unsigned long n, long d, Var vs[])
{
  unsigned long r = 2*n-1;
  unsigned long H = 3*n*n-3*n+1;
  long M = d*H;
  long o = d*r - (H-1)/2; /* offset in occupation array */
  unsigned long occupation[H]; /* if vs[i] has value x, occupation[x-o]==i, 
                                  if no vs[*] has value x, occupation[x-o]==r*r */
  unsigned long corners[] = {0, n-1, (n-1)*r+0, (n-1)*r+r-1, (r-1)*r+n-1, (r-1)*r+r-1};
  unsigned long i;
  //printf("(re)start\n");
  for (i=0; i<H; i++)
    occupation[i] = r*r;
  
  unsigned int change= 0b10;
  do {
    /* deal with the alldifferent constraint */
    if( change & 0b10 ) {
      for (i=0; i<r*r; i++) {
        Var *v = &vs[i];
        if (v->lo == v->hi && occupation[v->lo-o] != i) {
          if (occupation[v->lo-o] < r*r)
            return 0; /* another variable has the same value */
          occupation[v->lo-o] = i; /* occupy v->lo */
        }
      }
    }
    change= 0;

    /* now propagate the alldifferent results to the bounds */

    unsigned int alldiffRestart;
    do {
      alldiffRestart= 0;

      for (i=0; i<r*r; i++) {
        Var *v = &vs[i];
        if (v->lo < v->hi) {
          // This loop tries to improve the variable repeatedly
          do {

            // The current lower bound is impossible because the value is already fixed
            // by another variable -> try to move it up
            if (occupation[v->lo-o] < r*r) {
              v->lo++;
              if( v->lo == v->hi ) {
                if( occupation[v->lo-o] < r*r ) {
                  return 0;
                }
                occupation[v->lo-o]= i;

                // Restart the for loop
                alldiffRestart= 1;
                break;
              }
              // Try to improve again -> restart while loop
              continue;
            }

            // The current upper bound is impossible because the value is already fixed
            // by another variable -> try to move it down
            if (occupation[v->hi-o] < r*r) {
              v->hi--;
              if( v->lo == v->hi ) {
                if( occupation[v->lo-o] < r*r ) {
                  return 0;
                }
                occupation[v->lo-o]= i;
                
                // Restart the for loop
                alldiffRestart= 1;
                break;
              }
              // Try to improve again -> restart while loop
              continue;
            }

            // End the while loop if no improvements happened
            break;
          } while( 1 );
        }
      }

    } while( alldiffRestart );

    /* the < constraints; all other corners are smaller than the first
      one (eliminate rotational symmetry) */
    for (i=1; i<sizeof(corners)/sizeof(corners[0]); i++) {
      int f = lessthan(&vs[corners[0]],&vs[corners[i]]);
      if (f== NO_SOLUTION)
        return 0;
      if (f== DID_CHANGE)
        change |= 0b10;
    }
    /* eliminate the mirror symmetry between the corners to the right
      and left of the first corner */
    {
      int f = lessthan(&vs[corners[2]],&vs[corners[1]]); 
      if (f== NO_SOLUTION) 
        return 0;
      if (f== DID_CHANGE) 
        change|= 0b10;
    }
  
    /* sum constraints: each line and diagonal sums up to M */
    /* line sum constraints */
    {
      unsigned int i, j;
      for (i=0; i<r; i++) {
        unsigned long nv= min(i+n,r+n-i-1); // number of variables in this line/column/diagonal
        Var* linePtr= vs+r*i+max(0,i+1-n);
        Var* columnPtr= vs+i+max(0,i+1-n)*r;
        Var* diagonalPtr= vs-n+1+i+max(0,n-i-1)*(r+1);

        // Reset all hi and lo sum offsets to the expected sum
        long lineHi= M, columnHi= M, diagonalHi= M;
        long lineLo= M, columnLo= M, diagonalLo= M;

        Var *line, *column, *diagonal;
        line= linePtr;
        column = columnPtr;
        diagonal = diagonalPtr;
      
        // Compute the hi and lo offsets to the expected sum
        for (j=0; j<nv; j++) {
          assert(line < vs+r*r);
          assert(line->id >= 0);
          lineHi -= line->lo;
          lineLo -= line->hi;
          line++;

          assert(column < vs+r*r);
          assert(column->id >= 0);
          columnHi -= column->lo;
          columnLo -= column->hi;
          column+= r;

          assert(diagonal < vs+r*r);
          assert(diagonal->id >= 0);
          diagonalHi -= diagonal->lo;
          diagonalLo -= diagonal->hi;
          diagonal+= r+1;
        }


        line= linePtr;
        column= columnPtr;
        diagonal= diagonalPtr;
        
        // Re-add each hi and lo per variable and try setting tighter boundaries
        for (j=0; j<nv; j++) {
          {
            int f = sethi(line, lineHi+line->lo); /* readd vp->lo to get an upper bound of vp */
            if (f != NO_CHANGE) {
              if(f== DID_CHANGE) {
                if( line->hi == line->lo ) {
                  if( occupation[line->lo-o] < r*r ) {
                    return 0;
                  }
                  occupation[line->lo-o]= line- vs;
                }

                change |= 0b1;
              } else 
                return 0;
            }

            f = setlo(line, lineLo+line->hi); /* likewise, readd vp->hi */
            if (f != NO_CHANGE) {
              if(f== DID_CHANGE) {
                if( line->hi == line->lo ) {
                  if( occupation[line->lo-o] < r*r ) {
                    return 0;
                  }
                  occupation[line->lo-o]= line- vs;
                }

                change |= 0b1;
              } else 
                return 0;
            }
            line++;
          }

          {
            int f = sethi(column, columnHi+column->lo); /* readd vp->lo to get an upper bound of vp */
            if (f != NO_CHANGE) {
              if(f== DID_CHANGE) {
                if (column->hi == column->lo) {
                  if (occupation[column->lo - o] < r * r) {
                    return 0;
                  }
                  occupation[column->lo - o] = column - vs;
                }

                change |= 0b1;
              } else 
                return 0;
            }
            f = setlo(column, columnLo+column->hi); /* likewise, readd vp->hi */
            if (f != NO_CHANGE) {
              if(f== DID_CHANGE) {
                if( column->hi == column->lo ) {
                  if( occupation[column->lo-o] < r*r ) {
                    return 0;
                  }
                  occupation[column->lo - o] = column - vs;
                }

                change |= 0b1;
              } else 
                return 0;
            }
            column+= r;
          }

          {
            int f = sethi(diagonal, diagonalHi+diagonal->lo); /* readd vp->lo to get an upper bound of vp */
            if (f != NO_CHANGE) {
              if(f== DID_CHANGE) {
                if( diagonal->hi == diagonal->lo ) {
                  if( occupation[diagonal->lo-o] < r*r ) {
                    return 0;
                  }
                  occupation[diagonal->lo - o] = diagonal - vs;
                }

                change |= 0b1;
              } else 
                return 0;
            }
            f = setlo(diagonal, diagonalLo+diagonal->hi); /* likewise, readd vp->hi */
            if (f != NO_CHANGE) {
              if(f== DID_CHANGE) {
                if( diagonal->hi == diagonal->lo ) {
                  if( occupation[diagonal->lo-o] < r*r ) {
                    return 0;
                  }
                  occupation[diagonal->lo-o]= diagonal- vs;
                }

                change |= 0b1;
              } else 
                return 0;
            }
            diagonal+= r+1;
          }
        }
      }
    }
  } while( change );
  return 1;
}

static void printhexagon(unsigned long n, Var vs[])
{
  unsigned long i,j;
  unsigned r=2*n-1;
  for (i=0; i<r; i++) {
    unsigned long l=0;
    unsigned long h=r;
    if (i+1>n)
      l = i+1-n;
    if (i+1<n)
      h = n+i;
    for (j=h-l; j<r; j++)
      printf("    ");
    for (j=l; j<h; j++) {
      assert(i<r);
      assert(j<r);
      Var *v=&vs[i*r+j];
      assert(v->lo <= v->hi);
#if 0
      printf("%6ld  ",v->id);
#else
      if (v->lo < v->hi)
        printf("%4ld-%-3ld",v->lo,v->hi);
      else
        printf("%6ld  ",v->lo);
#endif
    }
    printf("\n");
  }
}

/* assign values to vs[index] and all later variables in vs such that
   the constraints hold */
static void labeling(unsigned long n, long d, Var vs[], unsigned long remaining[], unsigned long numRemaining, unsigned long numPreorderedRemaining)
{
  long i;
  unsigned long r = 2*n-1;
  if ( !numRemaining ) {
    printhexagon(n,vs);
    solutions++;
    leafs++;
    printf("leafs visited: %lu\n\n",leafs);
    return;
  }

  Var *vp;  
  if( numRemaining > numPreorderedRemaining ) {
    vp= vs+ remaining[--numRemaining];

  } else {
    // Find the var with the highest lower bound
    vp= vs+ remaining[0];
    unsigned long takeIndex= 0;
    for( i= 1; i<numRemaining; i++ ) {
      if( vs[remaining[i]].lo > vp->lo ) {
        vp= vs+ remaining[i];
        takeIndex = i;
      }
    }

    // Unstable take vp from array of remaining vars
    remaining[takeIndex]= remaining[--numRemaining];
  }

  // Allocate space on stack for new variable states
  Var newvs[r*r];
  long hi= vp->hi, lo= vp->lo;
  long range= hi - lo;
  
  // Do not further bisect boundaries if a value would get fixed (lo == hi)
  if( range < 4 ) {
    
    // Try the remaining values iteratively
    for (i = lo; i <= hi; i++) {
      Var* newvp=newvs+(vp-vs);
      // memmove(newvs,vs,r*r*sizeof(Var));
      for( long j = 0; j < r*r; j++ ) {
        newvs[j]= vs[j];
      }

      newvp->lo = i;
      newvp->hi = i;
      
      if (solve(n,d,newvs))
        labeling(n, d, newvs, remaining, numRemaining, numPreorderedRemaining);
      else
        leafs++;
    }

    // Append the taken variable index back onto the array of remaining vars
    remaining[numRemaining++]= vp-vs;
    return;
  }

  // Bisect the boundary range of the variable by calling labeling twice
  // The range is split into (L, M) and (M+1, H)
  long middle= lo+ range / 2;

  // Append the taken variable index back to the array before calling labeling,
  // as we will only split its range and it needs to be retaken later
  remaining[numRemaining++]= vp-vs;

  // Split range (L, M)
  Var* newvp=newvs+(vp-vs);
  // memmove(newvs,vs,r*r*sizeof(Var));
  for( long j = 0; j < r*r; j++ ) {
    newvs[j]= vs[j];
  }
  newvp->lo = lo;
  newvp->hi = middle;
  
  if (solve(n,d,newvs))
    labeling(n, d, newvs, remaining, numRemaining, numPreorderedRemaining);
  else
    leafs++;

  // Split range (M+1, H)
  // memmove(newvs,vs,r*r*sizeof(Var));
  for( long j = 0; j < r*r; j++ ) {
    newvs[j]= vs[j];
  }
  newvp->lo= middle+1;
  newvp->hi= hi;
  if (solve(n,d,newvs))
    labeling(n, d, newvs, remaining, numRemaining, numPreorderedRemaining);
  else
    leafs++;
}

static Hexagon makehexagon(unsigned long n, long d)
{
  unsigned long i,j;
  unsigned long r = 2*n-1;
  unsigned long H = 3*n*n-3*n+1;
  
  Var *vs = (Var*) calloc(r*r,sizeof(Var));
  unsigned char *usageMatrix= (unsigned char*) calloc(r*r, sizeof(unsigned char));
#ifndef NDEBUG
  unsigned long id = 0;
#endif
  for (i=0; i<r*r; i++) {
    Var *v = &vs[i];
    unsigned char *m= &usageMatrix[i];
#ifndef NDEBUG
    v->id = -1;
#endif
    *m= 0;
    v->lo = 1;
    v->hi = 0;
  }
  for (i=0; i<r; i++) {
    unsigned long l=0;
    unsigned long h=r;
    if (i+1>n)
      l = i+1-n;
    if (i+1<n)
      h = n+i;
    for (j=l; j<h; j++) {
      assert(i<r);
      assert(j<r);
      Var *v=&vs[i*r+j];
      unsigned char* m= &usageMatrix[i*r+j];
      assert(v->lo>v->hi);
#ifndef NDEBUG
      v->id = id++;
#endif
      *m= 1;
      v->lo = d*r - (H-1)/2;
      v->hi = d*r + (H-1)/2;
    }
  }
  Hexagon hexagon= { vs, usageMatrix };
  return hexagon;
}

int main(int argc, char *argv[])
{
  unsigned long i;
  unsigned long j=0;
  unsigned long n;
  long d;
  if (argc < 3) {
    fprintf(stderr, "Usage: %s <order> <deviation> <value> ... <value>\n", argv[0]);
    exit(1);
  }
  n = strtoul(argv[1],NULL,10);
  if (n<1) {
    fprintf(stderr, "order must be >=1\n");
    exit(1);
  }
  d = strtol(argv[2],NULL,10);
  Hexagon hexagon = makehexagon(n,d);
  Var *vs= hexagon.vs;
  unsigned char *usageMatrix= hexagon.usageMatrix;
  for (i=3; i<argc; i++) {
    while ( !usageMatrix[j] )
      j++;
    vs[j].lo = vs[j].hi = strtol(argv[i],NULL,10);
    j++;
  }

  unsigned long r= 2*n-1;
  unsigned long H= 3*n*n-3*n+1;
  unsigned long *remaining= (unsigned long*) calloc(H, sizeof(unsigned long));
  unsigned long numRemaining= 0;
  for(i= 0; i < r*r; i++ ) {
    if( usageMatrix[i] && vs[i].lo != vs[i].hi ) {
      remaining[ numRemaining++ ]= i;
    }
  }

  // Index of last pre-ordered element or array length if none are pre-ordered
  unsigned long numPreorderedRemaining= numRemaining;
  
  unsigned long corners[] = {0, n-1, (n-1)*r+0, (n-1)*r+r-1, (r-1)*r+n-1, (r-1)*r+r-1};
  for(i = 0; i!= sizeof(corners)/sizeof(unsigned long); i++) {
    for( j= 0; j< numPreorderedRemaining; j++ ) {
      if( remaining[j] == corners[i] ) {
        numPreorderedRemaining--;
        unsigned long temp= remaining[j];
        remaining[j]= remaining[numPreorderedRemaining];
        remaining[numPreorderedRemaining]= temp;
        break;
      }
    }
    
    // Preorder a single node to kick start the heuristic
    if( numRemaining - numPreorderedRemaining >= 1 ) {
      break;
    }
  }

  // for( i= 0; i!= numRemaining; i++) {
  //   printf("remaining [%ld]: %ld (corner %d)\n", i, remaining[i], i >= numPreorderedRemaining);
  // }

  labeling(n,d,vs, remaining, numRemaining, numPreorderedRemaining);
  printf("%lu solution(s), %lu leafs visited\n",solutions, leafs);
  //(void)solve(n, d, vs);
  //printhexagon(n, vs);
  return 0;
}
