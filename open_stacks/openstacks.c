/* ---------------------------------------------------------------------------
   Simple dynamic programming solution to challenge problem

   Peter Stuckey, May 2004

   Input format
-----------------------------
   [OPT] Name of benchmark on one line
   number-of-customers  number-of-products
   
   player 1: 0-1 (number-of-products) 
   player 2: 0-1 (number-of-products) 
   ...
   player n: 0-1 (number-of-products) 
 
-------------------------------
Example the challenge-small problem
-------------------------------

5 9

1 1 0 1 0 1 1 0 1  
1 1 0 1 1 1 0 1 0  
1 1 0 0 0 0 1 1 0  
1 0 0 0 1 1 0 0 1  
0 0 1 0 1 1 1 1 0  

-------------------------------

Returns the order where the minimum number
of customers need to be having their orders stacked
at the same time.

Example the challenge-small problem
-------------------------------
lowerbound = 4, upperbound = 5
mincost = 5, ccc = 171,loopcount=926

FLAGS:
     -a: A* algorithm, use an A* approach to the call based DP
     -b: Binary Chop: try finding a solution in the first half of
         lowerbound to upperbound, if not in first half of remainder, etc.
     -c: Clique lowerbounding: use maximal clique detected as a lowerbound.
     -d: make definite choices, that must be optimal
     -e: astar algorithm with hueristic 11
     -f: use finish tie breaker in A* algorithm
     -h: Use heuristics to give upper bound on solution
     -i n: iteration limit, most calls to mincost
     -l n: Lower bound: set the lower bound to be at least n
     -n: assume no name in the first line of the file
     -p: Preprocess input to remove products which are subsets of
         other products (in terms of customers)
     -s: Stepwise: try finding a solution for each value from
         lowerbound to upperbound
     -t: show statistics of operations
     -u n: Upper bound: set the upper bound to be at most n
     -v: Verbose output: show the actual solution
     -w: backwards stepwise
     -x: Extra verbose output: show solutions on the preprocessed problem

===============================================================================
   FOR the CHALLENGE PROBLEMS IT WAS COMPILED AS

       cc -DLARGE -DLOWMEM -O3 -lm

   AND RUN WITH FLAGS

       -a -h -p -c -t -g -w -d -i 33554432
   
===============================================================================
---------------------------------------------------------------------------- */
#include <math.h>
#include <stdio.h>
#include <sys/time.h>
#include <sys/resource.h>

struct rusage starttime,optimaltime,totaltime,runtime,endtime,opttime;


/* #define DEBUG */

int hashcount = 0;
int ucount = 0;

typedef struct twothings {
  long long high, low;
} SET;

#define ARRAYPRODUCTS 128
#define MAXPRODUCTS 128
#define MAXCUSTOMERS 128
#define MAXBIT 64

#define TABLESIZE        134217728  /* 2^27 */

/******************************* LINEAR CHAINING ****************************/
typedef struct entry {
  SET p;
  int opt;
  struct entry *next;
} ENTRY, *EP;

EP hsh[TABLESIZE];

#define max(a,b)  ((a) > (b) ? (a) : (b) )
#define minn(a,b)  ((a) < (b) ? (a) : (b) )
  
char name[100];

int ccc = 0;
int optccc = 0;

int LIMIT = 0;

int loopcount = 0;
int unioncount = 0;
int bitscount = 0;
int reuse = 0;
int definite = 0;

int cost[TABLESIZE];

int orig_playbit[ARRAYPRODUCTS][MAXCUSTOMERS];
int playbit[ARRAYPRODUCTS][MAXCUSTOMERS];

SET orig_plays[ARRAYPRODUCTS];
SET plays[ARRAYPRODUCTS];

int order[ARRAYPRODUCTS];
int orig_order[ARRAYPRODUCTS];

int rep[ARRAYPRODUCTS];
int orep[ARRAYPRODUCTS];

int upperbound;
int lowerbound;
int given_upperbound = 0;
int given_lowerbound = 0;
int global_upperbound = MAXCUSTOMERS + 1;
int global_lowerbound = 0;


#define in(i,S) ( (i) < 64 ? bit[i] & S.low : bit[(i)-64] & S.high ) 

#define union(S1,S2,S) { S.high = S1.high | S2.high ; S.low = S1.low | S2.low; } 

#define nonempty(S) ( S.low | S.high )

#define empty(S) ( !(S.low | S.high) )

#define emptyset(S)  { S.high = 0; S.low = 0; }

#define neg(S,N) { N.high = ~S.high; N.low = ~S.low; }

#define intersect(S1,S2,S) {S.high = S1.high & S2.high; S.low = S1.low & S2.low; }

#define subset(S1,S2) ( (S1.low == (S1.low & S2.low)) && (S1.high == (S1.high & S2.high)))

#define removebit(i,S0,S) { S = S0; if (i < 64) S.low = S.low & ~bit[i]; else S.high = S.high & ~bit[i-64]; } 

#define addbit(i,S0,S) { S = S0; if (i < 64) S.low = S.low | bit[i]; else S.high = S.high | bit[i-64]; } 

#define notequal(S1,S2) (S1.low != S2.low || S1.high != S2.high) 
#define equal(S1,S2) (S1.low == S2.low && S1.high == S2.high) 

#define intersects(S1,S2) ( (S1.low & S2.low) || (S1.high & S2.high)) 
int totalcost;

#define universe(S) { S.high = -1; S.low = -1; }

long long bit[64];

void printarr(int SIZE, int a[SIZE])
{
  int i;
  for (i = 0; i < SIZE; i++)
    printf("%5d",a[i]);
  printf("\n");
}

void printbit(int nbits, SET n)
{
  int  i;
  for (i = nbits-1; i >= 0; i--)
    if (in(i,n)) printf("1");
    else printf("0");
}

int CUSTOMERS;

int PRODUCTS;



int hash(SET p) {
  int i;
  EP  r;
  unsigned long long q;

#ifdef DEBUG
  printf("hash (");
  printbit(CUSTOMERS,p);
  printf(")\n");
#endif

  q = p.low;
  i = q % TABLESIZE;
  /*  printf("h %d\n",i); */
  r = hsh[i];
  while (r && (r->p.high != p.high || r->p.low != p.low))
    r = r->next;
  if (!r) return 0;
  return r->opt;
}

int hashset(SET p, int opt) {
  int i;
  EP  r;
  unsigned long long q;

#ifdef DEBUG
  printf("hashset (");
  printbit(CUSTOMERS,p);
  printf(",%d)\n",opt);
#endif

  q = p.low;
  i = q % TABLESIZE;
  /*  printf("hs %d\n",i); */
  r = hsh[i];
  while (r && (r->p.high != p.high || r->p.low != p.low))
    r = r->next;
  if (!r) {
    r = (EP) malloc(sizeof(ENTRY));
    r->p = p;
    r->opt = opt;
    r->next = hsh[i];
    hashcount++;
    hsh[i] = r;
  } else
    if (opt && r->opt) { printf("ERROR: hash already set\n"); exit(1); }
  r->opt = opt;
  return r->opt;
}

EP faillist = NULL;
EP succlist = NULL;

int add_fail(SET p) {
  EP  r;

#ifdef DEBUG
  printf("add_fail (");
  printbit(CUSTOMERS,p);
  printf(")\n");
#endif
  r = (EP) malloc(sizeof(ENTRY));
  r->p = p;
  r->opt = 0;
  r->next = faillist;
  faillist = r;
}

int add_succ(SET p) {
  EP  r;

#ifdef DEBUG
  printf("add_succ (");
  printbit(CUSTOMERS,p);
  printf(")\n");
#endif

  r = (EP) malloc(sizeof(ENTRY));
  r->p = p;
  r->opt = 0;
  r->next = succlist;
  succlist = r;
}

int undo(EP list) {
  EP r,s;

  ucount++;
  r = list;
  while (r) {
#ifdef DEBUG
  printf("undo(");
  printbit(CUSTOMERS,r->p);
  printf(")\n");
#endif
    hashset(r->p, 0);
    s = r->next;
    free(r);
    r = s;
  }
}

/* free the list but dont undo */
int dontundo(EP list) {
  EP r,s;

  r = list;
  while (r) {
#ifdef DEBUG
  printf("dontundo(");
  printbit(CUSTOMERS,r->p);
  printf(")\n");
#endif
    s = r->next;
    free(r);
    r = s;
  }
}
      


SET ALLPRODUCTS;
int orig_CUSTOMERS;

int orig_PRODUCTS;

int orig_ALLPRODUCTS;

int use_heuristic = 0;
int use_preprocess = 0;
int verbose = 0;
int extra_verbose = 0;
int astar = 0;
int stepwise = 0;
int binarychop = 0;
int cliquef = 0;
int optpart = 0;
int lookprune = 0;
int showstats = 0;
int repeats = 1;
int noname = 0;
int maxfinish = 0;
int astar11 = 0;
int backstepwise = 0;
int segment = 0;
int definite_choice = 0;
int fail_undo = 0;
int succ_undo = 0;


SET unionp(SET pcs)
{
  int i;
  SET un;

  emptyset(un);
  if (empty(pcs)) return un;
  for (i = 0; i < PRODUCTS; i++) 
    if ( in(i,pcs) ) {
      union(un,plays[i],un);
    }
  unioncount++;
  return un;
}


int nbitsp(SET as)
{
  int c;
  long long word;

  word = as.high;
  for (c = 0; word; c++)
    {
      word &= word - 1; // clear the least significant bit set
    }
  word = as.low;
  for (; word; c++)
    {
      word &= word - 1; // clear the least significant bit set
    }
  bitscount++;
  return c;
}


/** A star version of mincost **/
int asmincost(SET prods) {
  int min = upperbound + 1;
  int i, tmp;
  SET previously_stacked;
  SET stacked_after;
  SET stacked_now;
  SET stacked_before;
  SET t1, t2;
  int number_stacks_now;
  int num_st_now[PRODUCTS];
  int tcost;
  int min_now;
  int min_i;


  if (empty(prods)) return 0;
  if (hash(prods)) {reuse++; return hash(prods);}
#ifdef DEBUG
  printf("asmincost(");
  printbit(PRODUCTS,prods);
  printf(")\n");
#endif
  /** First just work out the stacks now for each product i in prods **/
  stacked_after = unionp(prods);
  neg(prods, t1);
  intersect(t1,ALLPRODUCTS,t2);
  stacked_before = unionp(t2);
  for (i = 0; i < PRODUCTS; i++) {
#ifdef DEBUG
    printf("loop(%d) i=%d\n",prods,i);
#endif
    /* ignore already played pieces */
    if (!in(i,prods)) continue;
    num_st_now[i] = CUSTOMERS;
    loopcount++;
    /* update who has arrived */
    union(stacked_before,plays[i],previously_stacked);
    /* previously_stacked = stacked_before | plays[i]; */
    intersect(previously_stacked,stacked_after,stacked_now);
    /* stacked_now = previously_stacked & stacked_after; */
    number_stacks_now = nbitsp(stacked_now);
#ifdef DEBUG
    printf("asmincost(");
    printbit(PRODUCTS,prods);
    printf(") - i=%d, prev=",i);
    printbit(CUSTOMERS,previously_stacked);
    printf(" after=");
    printbit(CUSTOMERS,stacked_after);
    printf(" here=");
    printbit(CUSTOMERS,stacked_now);
    printf(" stacksnow=%d\n",number_stacks_now);
#endif
    if (definite_choice && subset(plays[i],stacked_before)) {
      /*** an optimal must start with this one **/
#ifdef DEBUG
      printf("DEFINITE CHOICE :");
      printbit(CUSTOMERS,stacked_before);
      printf(" sup ");
      printbit(CUSTOMERS,plays[i]);
      printf("\n");
#endif
      definite++;
      if (number_stacks_now < min) {
	removebit(i,prods,t1);
	tcost = asmincost(t1);
	tcost = max(number_stacks_now,tcost); 
	if (tcost < min) min = tcost;
      }
      /** UGLY but the easiest way **/
      goto FINISH;
    }
    if (number_stacks_now >= min) continue; /* cant be better */
    num_st_now[i] = number_stacks_now;
  }
  /** Second seach in order of the product with minimum stacks now **/
  /** stop if we have found as good as is globally possible) **/
  while (min > lowerbound) {
    /* Find the i with minimum number_stacks_now */
    min_now = min; 
    for (i = 0; i < PRODUCTS; i++) {
      if (!in(i,prods)) continue;
      if (num_st_now[i] < min_now) {
	min_i = i;
	min_now = num_st_now[i];
      }
    }
    /** if we cant find something better than current min finish */
    if (min_now == min) break;
    num_st_now[min_i] = CUSTOMERS; /* dont pick min_i again */ 
 #ifdef DEBUG
    printf("asmincost(");
    printbit(PRODUCTS,prods);
    printf(") - i=%d, stacksnow=%d\n",min_i,min_now);
#endif    
    removebit(min_i,prods,t1);
    tcost = asmincost(t1);
    tcost = max(min_now, tcost);
#ifdef DEBUG
    printf("asmincost(%d) - i=%d, tcost=%d\n",prods,i,tcost); 
#endif
    if (tcost < min) min = tcost;
  } 
    FINISH:
  ccc++;
  if (LIMIT && ccc > LIMIT) {
    printf("LIMIT %d EXCEEDED: %s",LIMIT,name); exit(1); }
  if (fail_undo && min == upperbound+1) {
    /** save the fake bound position **/
#ifdef DEBUG
    printf("undo min(%d) = %d\n",prods,min);
#endif
    add_fail(prods);
  } else if (succ_undo) {
    add_succ(prods);
  }
  hashset(prods,min);
#ifdef DEBUG
  printf("MIN(");
  printbit(PRODUCTS,prods);
  printf(") = %d\n",min);
#endif
  return min;
}


/** CUSTOMER GRAPH **/
SET cross[MAXCUSTOMERS];



/** A star version of mincost, with heuristic 11 **/
int asmincost11(SET prods) {
  int min = upperbound + 1;
  int i, j, k, tmp;
  SET previously_stacked;
  SET stacked_after;
  SET stacked_now;
  SET stacked_before;
  SET stacked_strictly_after;
  SET new_customers;
  int number_after;
  int min_cust;
  SET t1, t2, t3;
  int number_stacks_now;
  int num_st_now[PRODUCTS];
  int tcost;
  int min_now;
  int min_i;
  int counts[CUSTOMERS];
  int tmpcounts[CUSTOMERS];

  if (empty(prods)) return 0;
  if (hash(prods)) {reuse++; return hash(prods);}
#ifdef DEBUG
  printf("asmincost11(");
  printbit(PRODUCTS,prods);
  printf(")\n");
#endif


  /** First just work out the stacks now for each product i in prods **/
  stacked_after = unionp(prods);
  neg(prods, t1);
  intersect(t1,ALLPRODUCTS,t2);
  stacked_before = unionp(t2);
  for (j =0; j < CUSTOMERS; j++)
    counts[j] = 0;

  /* count the number of adjacent customers */
  for (i = 0; i < CUSTOMERS; i++)
    for (j = 0; j < CUSTOMERS; j++)
      if (!in(j,stacked_before) && in(j,cross[i]))
	counts[i]++;
#ifdef DEBUG
  printf("OCOUNTS:");
  for (j = 0; j < CUSTOMERS; j++)
    printf(" %d", counts[j]);
  printf("\n");
#endif

  for (i = 0; i < PRODUCTS; i++) {
#ifdef DEBUG
    printf("loop(%d) i=%d\n",prods,i);
#endif
    /* ignore already played pieces */
    if (!in(i,prods)) continue;
    num_st_now[i] = CUSTOMERS;
    loopcount++;
    /* update who has arrived */
    union(stacked_before,plays[i],previously_stacked);
    /* previously_stacked = stacked_before | plays[i]; */
    intersect(previously_stacked,stacked_after,stacked_now);
    /* stacked_now = previously_stacked & stacked_after; */
    number_stacks_now = nbitsp(stacked_now);
#ifdef DEBUG
    printf("asmincost11(");
    printbit(PRODUCTS,prods);
    printf(") - i=%d, prev=",i);
    printbit(CUSTOMERS,previously_stacked);
    printf(" after=");
    printbit(CUSTOMERS,stacked_after);
    printf(" here=");
    printbit(CUSTOMERS,stacked_now);
    printf(" stacksnow=%d\n",number_stacks_now);
#endif
    if (definite_choice && subset(plays[i],stacked_before)) {
      /*** an optimal must start with this one **/
#ifdef DEBUG
      printf("DEFINITE CHOICE :");
      printbit(CUSTOMERS,stacked_before);
      printf(" sup ");
      printbit(CUSTOMERS,plays[i]);
      printf("\n");
#endif
      definite++;
      if (number_stacks_now < min) {
	removebit(i,prods,t1);
	tcost = asmincost11(t1);
	tcost = max(number_stacks_now,tcost); 
	if (tcost < min) min = tcost;
      }
      /** UGLY but the easiest way **/
      goto FINISH;
    }
    removebit(i,prods,t1);
    stacked_strictly_after = unionp(t1);
    neg(stacked_before,t2);
    intersect(plays[i],t2,new_customers);
    intersect(stacked_strictly_after,previously_stacked,t3);
    number_after = nbitsp(t3);
    /* update the counts for each customer */
    for (j = 0; j < CUSTOMERS; j++)
      tmpcounts[j] = counts[j];
    for (j = 0; j < CUSTOMERS; j++)
      if (in(j,new_customers))
	for (k = 0; k <  CUSTOMERS; k++) {
	  if (in(j,cross[k])) tmpcounts[k]--;
	  if (!tmpcounts[k] && (!in(k,stacked_strictly_after)))
	    tmpcounts[k] = CUSTOMERS+1; /** customer is finished **/
	}
    /* find minimum number of neighbours */
    min_cust = CUSTOMERS+1;
    for (j = 0; j < CUSTOMERS; j++)
      if (tmpcounts[j] < min_cust) min_cust = tmpcounts[j];
    if (min_cust > CUSTOMERS) min_cust = 0;
#ifdef DEBUG
    printf("asmincost11(");
    printbit(PRODUCTS,prods);
    printf(") - i=%d, plays=",i);
    printbit(CUSTOMERS,plays[i]);
    printf(" prev=");
    printbit(CUSTOMERS,previously_stacked);
    printf(" after=");
    printbit(CUSTOMERS,stacked_after);
    printf(" strict_after=");
    printbit(CUSTOMERS,stacked_strictly_after);
    printf(" here=");
    printbit(CUSTOMERS,stacked_now);
    printf(" stacksnow=%d,number_after=%d,mincust=%d\n",
	   number_stacks_now,number_after,min_cust);
    printf("COUNTS:");
    for (j = 0; j < CUSTOMERS; j++)
      printf(" %d", tmpcounts[j]);
    printf("\n");
#endif
    number_stacks_now = max(number_stacks_now,number_after+min_cust);
    if (number_stacks_now >= min) continue; /* cant be better */
    num_st_now[i] = number_stacks_now;
  }
  /** Second seach in order of the product with minimum stacks now **/
  /** stop if we have found as good as is globally possible) **/
#ifdef DEBUG
  for (i = 0; i < PRODUCTS; i++)
    printf("YYY min = %d, min_now %d = %d\n", min, i, num_st_now[i]);
#endif
  while (min > lowerbound) {
    /* Find the i with minimum number_stacks_now */
    min_now = min; 
    for (i = 0; i < PRODUCTS; i++) {
      if (!in(i,prods)) continue;
      if (num_st_now[i] < min_now) {
	min_i = i;
	min_now = num_st_now[i];
      }
    }
    /** if we cant find something better than current min finish */
    if (min_now == min) break;
    num_st_now[min_i] = CUSTOMERS; /* dont pick min_i again */ 
 #ifdef DEBUG
    printf("asmincost11(");
    printbit(PRODUCTS,prods);
    printf(") - i=%d, stacksnow=%d\n",min_i,min_now);
#endif    
    removebit(min_i,prods,t1);
    tcost = asmincost11(t1);
    tcost = max(min_now, tcost);
#ifdef DEBUG
    printf("asmincost11(%d) - i=%d, tcost=%d\n",prods,i,tcost); 
#endif
    if (tcost < min) min = tcost;
  } 
    FINISH:
  ccc++;
  if (LIMIT && ccc > LIMIT) {
    printf("LIMIT %d EXCEEDED: %s",LIMIT,name); exit(1); }
  if (fail_undo && min == upperbound+1) {
    /** save the fake bound position **/
#ifdef DEBUG
    printf("undo min(%d) = %d\n",prods,min);
#endif
    add_fail(prods);
  } else if (succ_undo) {
    add_succ(prods);
  }
  hashset(prods,min);
#ifdef DEBUG
  printf("MIN(");
  printbit(PRODUCTS,prods);
  printf(") = %d\n",min);
#endif
  return min;
}




/** min stacks now breaking ties on finishes **/
int heuristic3(SET prods, int index) {
  int min = 0;
  int i;
  SET previously_stacked;
  SET stacked_after;
  SET stacked_before;
  SET stacked_now;
  SET stacked_strictly_after;
  int number_stacks_now;
  int closed_size;
  int num_st_now[PRODUCTS];
  int tcost;
  int min_now;
  int closed_now;
  int min_i;
  SET t1,t2,t3;

  while (nonempty(prods)) {
#ifdef DEBUG
    printf("heuristic(");
    printbit(PRODUCTS,prods);
    printf(")\n");
#endif
    /** First just work out the stacks now for each product i in prods **/
    min_now = CUSTOMERS+1;
    closed_now = -1;
    stacked_after = unionp(prods);
    neg(prods,t1);
    intersect(t1,ALLPRODUCTS,t2);
    stacked_before = unionp(t2);
    for (i = 0; i < PRODUCTS; i++) {
#ifdef DEBUG
      printf("heurloop(%d) i=%d\n",prods,i);
#endif
      /* ignore already played pieces */
      if (!in(i,prods)) continue;
      loopcount++;
      /* update who has arrived */
      union(stacked_before,plays[i],previously_stacked);
      /* previously_stacked = stacked_before | plays[i]; */
      intersect(previously_stacked,stacked_after,stacked_now);
      /* stacked_now = previously_stacked & stacked_after; */
      number_stacks_now = nbitsp(stacked_now);
      if (definite_choice && subset(plays[i],stacked_before)) {
	/*** an optimal must start with this one **/
#ifdef DEBUG
      printf("DEFINITE CHOICE :");
      printbit(CUSTOMERS,stacked_before);
      printf(" sup ");
      printbit(CUSTOMERS,plays[i]);
      printf("\n");
#endif
	min_i = i;
	min_now = number_stacks_now;
	break;
      }
      removebit(i,prods,t1);
      stacked_strictly_after = unionp(t1);
      neg(stacked_strictly_after,t1);
      intersect(t1,plays[i],t2);
      intersect(t2,stacked_before,t3);
      closed_size = nbitsp(t3);     
#ifdef DEBUG
      printf("heuristic(");
      printbit(PRODUCTS,prods);
      printf(") - i=%d, prev=",i);
      printbit(CUSTOMERS,previously_stacked);
      printf(" after=");
      printbit(CUSTOMERS,stacked_after);
      printf(" here=");
      printbit(CUSTOMERS,stacked_now);
      printf(" stacksnow=%d,closed=%d\n",number_stacks_now,closed_size);
#endif
      if (number_stacks_now < min_now ||
	  (number_stacks_now == min_now && closed_size > closed_now)) {
	min_i = i;
	min_now = number_stacks_now;
	closed_now = closed_size;
      }
    }
#ifdef DEBUG
    printf("heuristic(");
    printbit(PRODUCTS,prods);
    printf(") - i=%d, stacksnow=%d\n",min_i,min_now);
#endif    
    order[index++] = min_i;
    removebit(min_i,prods,prods);
    min = max(min,min_now);
  }
#ifdef DEBUG
  printf("HEUR(");
  printbit(PRODUCTS,prods);
  printf(") = %d\n",min);
#endif
  return min;
}


/** min stacks now breaking ties on finishe- treatign equal those less than min**/
int heuristic4(SET prods, int index) {
  int min = 0;
  int i;
  SET previously_stacked;
  SET stacked_after;
  SET stacked_before;
  SET stacked_now;
  SET stacked_strictly_after;
  int number_stacks_now;
  int closed_size;
  int num_st_now[PRODUCTS];
  int tcost;
  int min_now;
  int closed_now;
  int min_i;
  SET t1,t2,t3;

  while (nonempty(prods)) {
#ifdef DEBUG
    printf("heuristic(");
    printbit(PRODUCTS,prods);
    printf(")\n");
#endif
    /** First just work out the stacks now for each product i in prods **/
    min_now = CUSTOMERS+1;
    closed_now = -1;
    stacked_after = unionp(prods);
    neg(prods,t1);
    intersect(t1,ALLPRODUCTS,t2);
    stacked_before = unionp(t2);
    for (i = 0; i < PRODUCTS; i++) {
#ifdef DEBUG
      printf("heurloop(%d) i=%d\n",prods,i);
#endif
      /* ignore already played pieces */
      if (!in(i,prods)) continue;
      loopcount++;
      /* update who has arrived */
      union(stacked_before,plays[i],previously_stacked);
      /* previously_stacked = stacked_before | plays[i]; */
      intersect(previously_stacked,stacked_after,stacked_now);
      /* stacked_now = previously_stacked & stacked_after; */
      number_stacks_now = nbitsp(stacked_now);
      if (definite_choice && subset(plays[i],stacked_before)) {
	/*** an optimal must start with this one **/
#ifdef DEBUG
      printf("DEFINITE CHOICE :");
      printbit(CUSTOMERS,stacked_before);
      printf(" sup ");
      printbit(CUSTOMERS,plays[i]);
      printf("\n");
#endif
	min_i = i;
	min_now = number_stacks_now;
	break;
      }
      removebit(i,prods,t1);
      stacked_strictly_after = unionp(t1);
      neg(stacked_strictly_after,t1);
      intersect(t1,plays[i],t2);
      intersect(t2,stacked_before,t3);
      closed_size = nbitsp(t3);     
#ifdef DEBUG
      printf("heuristic(");
      printbit(PRODUCTS,prods);
      printf(") - i=%d, prev=",i);
      printbit(CUSTOMERS,previously_stacked);
      printf(" after=");
      printbit(CUSTOMERS,stacked_after);
      printf(" here=");
      printbit(CUSTOMERS,stacked_now);
      printf(" stacksnow=%d,closed=%d\n",number_stacks_now,closed_size);
#endif
      /* cant be better or doesnt increase the max stacks_sofar */
      if ((number_stacks_now < min_now && min_now > min) ||
	  (number_stacks_now <= min && closed_size > closed_now)) {
	min_i = i;
	min_now = number_stacks_now;
	closed_now = closed_size;
      }
      if (number_stacks_now > min_now && number_stacks_now > min) 
	continue;
      if (closed_size <= closed_now) continue; /* cant be better */
      min_i = i;
      min_now = number_stacks_now;
      closed_now = closed_size;
    }
#ifdef DEBUG
    printf("heuristic(");
    printbit(PRODUCTS,prods);
    printf(") - i=%d, stacksnow=%d\n",min_i,min_now);
#endif    
    order[index++] = min_i;
    removebit(min_i,prods,prods);
    min = max(min,min_now);
  }
#ifdef DEBUG
  printf("HEUR(");
  printbit(PRODUCTS,prods);
  printf(") = %d\n",min);
#endif
  return min;
}


/** Yuens heuristic 3 **/
int heuristic6(SET prods, int index) {
  int min = 0;
  int i;
  SET previously_stacked;
  SET stacked_after;
  SET stacked_before;
  SET stacked_now;
  int number_stacks_now;
  int tcost;
  int min_now;
  int intersection_size;
  int new_size;
  int cost_now, cost;
  int intersection_now;
  int min_i;
  SET t1,t2,t3;

  while (nonempty(prods)) {
#ifdef DEBUG
    printf("heuristic6(");
    printbit(PRODUCTS,prods);
    printf(")\n");
#endif
    /** First just work out the stacks now for each product i in prods **/
    min_now = CUSTOMERS+1;
    cost_now = -2*CUSTOMERS;
    stacked_after = unionp(prods);
    neg(prods,t1);
    intersect(t1,ALLPRODUCTS,t2);
    stacked_before = unionp(t2);
    for (i = 0; i < PRODUCTS; i++) {
#ifdef DEBUG
      printf("heurloop6(%d) i=%d\n",prods,i);
#endif
      /* ignore already played pieces */
      if (!in(i,prods)) continue;
      loopcount++;
      /* update who has arrived */
      union(stacked_before,plays[i],previously_stacked);
      /* previously_stacked = stacked_before | plays[i]; */
      intersect(previously_stacked,stacked_after,stacked_now);
      /* stacked_now = previously_stacked & stacked_after; */
      number_stacks_now = nbitsp(stacked_now);
      if (definite_choice && (subset(plays[i],stacked_before))) {
	/*** an optimal must start with this one **/
#ifdef DEBUG
	printf("DEFINITE CHOICE :");
	printbit(CUSTOMERS,stacked_before);
	printf(" sup ");
	printbit(CUSTOMERS,plays[i]);
	printf("\n");
#endif
	min_i = i;
	min_now = number_stacks_now;
	break;
      }
      intersect(plays[i],stacked_before,t1);
      intersection_size = nbitsp(t1);
      neg(stacked_before,t2);
      intersect(plays[i],t2,t3);
      new_size = nbitsp(t3);
      cost = intersection_size - new_size;
#ifdef DEBUG
      printf("heuristic6(");
      printbit(PRODUCTS,prods);
      printf(") - i=%d, prev=",i);
      printbit(CUSTOMERS,previously_stacked);
      printf(" after=");
      printbit(CUSTOMERS,stacked_after);
      printf(" here=");
      printbit(CUSTOMERS,stacked_now);
      printf(" stacksnow=%d,cost=%d\n",number_stacks_now,cost);
#endif
     if (cost > cost_now) {
	min_i = i;
	min_now = number_stacks_now;
	cost_now = cost;
      }
    }
#ifdef DEBUG
    printf("heuristic6(");
    printbit(PRODUCTS,prods);
    printf(") - i=%d, stacksnow=%d\n",min_i,min_now);
#endif    
    order[index++] = min_i;
    removebit(min_i,prods,prods);
    min = max(min,min_now);
  }
#ifdef DEBUG
  printf("HEUR(");
  printbit(PRODUCTS,prods);
  printf(") = %d\n",min);
#endif
  return min;
}


/** REwarding finishes or almost finishes 2^-k costs **/
int heuristic7(SET prods, int index) {
  int min = 0;
  int i, j;
  SET previously_stacked;
  SET stacked_after;
  SET stacked_before;
  SET stacked_now;
  int number_stacks_now;
  int tcost;
  int min_now;
  int intersection_size;
  int new_size;
  float cost_now, cost;
  int intersection_now;
  int min_i;
  int counts[CUSTOMERS];
  int maxcount[CUSTOMERS];
  SET t1,t2,t3;

  for (j =0; j < CUSTOMERS; j++)
    counts[j] = 0;

  for (i = 0; i < PRODUCTS; i++)
    for (j =0; j < CUSTOMERS; j++)
      if (in(j,plays[i]))
	counts[j]++;

  for (j =0; j < CUSTOMERS; j++)
    maxcount[j] = counts[j];

#ifdef DEBUG
  printf("COUNTS:");
  for (j = 0; j < CUSTOMERS; j++)
    printf(" %d", counts[j]);
  printf("\n");
#endif

  while (nonempty(prods)) {
#ifdef DEBUG
    printf("heuristic7(");
    printbit(PRODUCTS,prods);
    printf(")\n");
#endif
    /** First just work out the stacks now for each product i in prods **/
    min_now = CUSTOMERS+1;
    cost_now = -CUSTOMERS;
    stacked_after = unionp(prods);
    neg(prods,t1);
    intersect(t1,ALLPRODUCTS,t2);
    stacked_before = unionp(t2);
    for (i = 0; i < PRODUCTS; i++) {
#ifdef DEBUG
      printf("heurloop7(%d) i=%d\n",prods,i);
#endif
      /* ignore already played pieces */
      if (!in(i,prods)) continue;
      loopcount++;
      /* update who has arrived */
      union(stacked_before,plays[i],previously_stacked);
      /* previously_stacked = stacked_before | plays[i]; */
      intersect(previously_stacked,stacked_after,stacked_now);
      /* stacked_now = previously_stacked & stacked_after; */
      number_stacks_now = nbitsp(stacked_now);
      if (definite_choice && (subset(plays[i],stacked_before))) {
	/*** an optimal must start with this one **/
#ifdef DEBUG
	printf("DEFINITE CHOICE :");
	printbit(CUSTOMERS,stacked_before);
	printf(" sup ");
	printbit(CUSTOMERS,plays[i]);
	printf("\n");
#endif
	min_i = i;
	min_now = number_stacks_now;
	break;
      }
      cost = 0;
      for (j = 0; j < CUSTOMERS; j++)
	if (in(j,plays[i]))
	  cost += powf(2.0,(- counts[j]));
#ifdef DEBUG
      printf("heuristic(");
      printbit(PRODUCTS,prods);
      printf(") - i=%d, prev=",i);
      printbit(CUSTOMERS,previously_stacked);
      printf(" after=");
      printbit(CUSTOMERS,stacked_after);
      printf(" here=");
      printbit(CUSTOMERS,stacked_now);
      printf(" stacksnow=%d,cost=%f\n",number_stacks_now,cost);
#endif
      /*      if (number_stacks_now < min_now ||
	      (number_stacks_now == min_now && cost > cost_now)) { */
      /* if (cost > cost_now || cost == cost_now && number_stacks_now < min_now ) { */
      if (number_stacks_now < min_now || number_stacks_now == min_now && cost > cost_now) {
	min_i = i;
	min_now = number_stacks_now;
	cost_now = cost;
      }
    }
#ifdef DEBUG
    printf("heuristic7(");
    printbit(PRODUCTS,prods);
    printf(") - i=%d, stacksnow=%d, cost=%f, (",min_i,min_now,cost_now);
    printbit(CUSTOMERS,plays[min_i]);
    printf(")\n");
#endif    
    order[index++] = min_i;
    for (j = 0; j < CUSTOMERS; j++)
      if (in(j,plays[min_i]))
	counts[j]--;
#ifdef DEBUG
    printf("COUNTS:");
    for (j = 0; j < CUSTOMERS; j++)
      printf(" %d", counts[j]);
    printf("\n");
#endif
    removebit(min_i,prods,prods);
    min = max(min,min_now);
  }
#ifdef DEBUG
  printf("HEUR(");
  printbit(PRODUCTS,prods);
  printf(") = %d\n",min);
#endif
  return min;
}


/** Becceneri **/
int heuristic10(SET prods, int index) {
  int min = 0;
  int i,j;
  SET previously_stacked;
  SET stacked_after;
  SET stacked_before;
  SET stacked_now;
  int number_stacks_now;
  int tcost;
  int min_now;
  int intersection_size;
  int new_size;
  int cost_now, cost;
  int intersection_now;
  int min_i;
  SET t1,t2,t3,t4;

  int omega[CUSTOMERS];
  int arcx[CUSTOMERS*CUSTOMERS];
  int arcy[CUSTOMERS*CUSTOMERS];
  int open[CUSTOMERS];
  SET lcross[CUSTOMERS];
  SET nowopen;

  int k,n1,n2;
  int setvk,setv2;

  int arccount = 0;
  int s = 0;
  int arcs = 0;

  emptyset(nowopen);

  for (j = 0; j < CUSTOMERS; j++) 
    emptyset(lcross[j]);
  for (i = 0; i < PRODUCTS; i++)
    if (in(i,prods)) { /* restrict to local prods */
      if (nbitsp(plays[i]) > min) min = nbitsp(plays[i]);
      for (j = 0; j < CUSTOMERS; j++) 
	if (in(j,plays[i])) {
	  union(plays[i],lcross[j],lcross[j]);
	  /* lcross[j] = lcross[j] | plays[i]; */
	}
    }
  for (j = 0; j < CUSTOMERS; j++) 
    removebit(j,lcross[j],lcross[j]);

#ifdef DEBUG
  for (i = 0; i < CUSTOMERS; i++) {
    printf("%2d:",i);
    printbit(CUSTOMERS,lcross[i]);
    for (j = 0; j < CUSTOMERS; j++) 
      if (in(j,lcross[i]))
	printf(" X ");
      else
	printf(" . ");
    printf("\n");
  }
#endif

  for (i = 0; i < CUSTOMERS; i++) {
    omega[i] = 0;
    open[i] = 0;
    for (j = 0; j < CUSTOMERS; j++)
      if (i != j && (in(j,lcross[i]))) {
	omega[i]++;
	if (i < j) arcs++;
      }
  }
  for (i = 0; i < CUSTOMERS; i++) 
    if (!omega[i]) omega[i] = CUSTOMERS;
    
  while (s != arcs) {
#ifdef DEBUG
    for (i = 0; i < CUSTOMERS; i++) printf("%d ",omega[i]); printf("\n");
    for (i = 0; i < CUSTOMERS; i++) printf("%d ",open[i]); printf("\n");
    for (i = 0; i < CUSTOMERS; i++) {
      printbit(CUSTOMERS,lcross[i]); 
      printf(" ");
    }
    printf("\n");
#endif    

    k = -1;
    setvk = CUSTOMERS;
    for (i = 0; i < CUSTOMERS; i++)
      if (omega[i] < setvk) {
	k = i;
	setvk = omega[i];
      }
#ifdef DEBUG
    printf("k=%d, setvk=%d\n",k,setvk);
#endif
    setv2 = CUSTOMERS;
    for (i = 0; i < CUSTOMERS; i++) {
      if (omega[i] != setvk) continue;
      for (j = 0; j < CUSTOMERS; j++)
	if (i != j)
	  if (in(j,lcross[i]) && omega[j] < setv2) {
	    n1 = i;
	    n2 = j;
	    setv2 = omega[j];
	  }
    }
#ifdef DEBUG
    printf("add arc (%d,%d)\n",n1,n2);
#endif
    s++;
    arcx[arccount] = n1;
    arcy[arccount] = n2;
    arccount++;
    open[n1] = 1;
    removebit(n2,lcross[n1],lcross[n1]);
    omega[n1]--;
    open[n2] = 1;
    removebit(n1,lcross[n2],lcross[n2]);
    omega[n2]--;
    if (!omega[n1]) { open[n1] = 0; omega[n1] = CUSTOMERS; }
    if (!omega[n2]) { open[n2] = 0; omega[n2] = CUSTOMERS; }
    
    for (i = 0; i < CUSTOMERS; i++) 
      if (open[i])
	for (j = i+1; j < CUSTOMERS; j++)
	  if (open[j] && (in(j,lcross[i]))) {
	    s++;
#ifdef DEBUG
	    printf("[E] add arc (%d,%d)\n",i,j);
#endif
	    arcx[arccount] = i;
	    arcy[arccount] = j;
	    arccount++;
	    open[i] = 1;
	    removebit(j,lcross[i],lcross[i]);
	    omega[i]--;
	    open[j] = 1;
	    removebit(i,lcross[j],lcross[j]);
	    omega[j]--;
	    if (!omega[i])  { open[i] = 0; omega[i] = CUSTOMERS; }
	    if (!omega[j])  { open[j] = 0; omega[j] = CUSTOMERS; }
	  }
  }

  for (i = 0; i < arcs; i++) {
    addbit(arcx[i],nowopen,nowopen);
    addbit(arcy[i],nowopen,nowopen);
    /*
    nowopen = nowopen | bit[arcx[i]];
    nowopen = nowopen | bit[arcy[i]];
    */
    for (j = 0; j < PRODUCTS; j++)
      if (in(j,prods)) 
	if (subset(plays[j],nowopen)) {
	  order[index++] = j;
	  stacked_after = unionp(prods);
	  neg(prods,t1);
	  intersect(t1,ALLPRODUCTS,t2);
	  stacked_before = unionp(t2);
	  union(stacked_before,plays[j],previously_stacked);
	  intersect(previously_stacked,stacked_after,stacked_now);
	  number_stacks_now = nbitsp(stacked_now);
	  min = max(min,number_stacks_now);
	  removebit(j,prods,prods);
	}
  }     

  return min;
}



/** using max(number_stacks_now,min to complete) **/
int heuristic11(SET prods, int index) {
  int min = 0;
  int i, j, k;
  SET previously_stacked;
  SET stacked_after;
  SET stacked_before;
  SET stacked_now;
  SET stacked_strictly_after;
  SET new_customers;
  int number_stacks_now;
  int number_after;
  int min_cust;
  int tcost;
  int min_now;
  int intersection_size;
  int new_size;
  float cost_now, cost;
  int intersection_now;
  int min_i;
  int counts[CUSTOMERS];
  int maxcount[CUSTOMERS];
  SET t1,t2,t3;

  for (j =0; j < CUSTOMERS; j++)
    counts[j] = 0;

  /* count the number of adjacent customers */
  for (i = 0; i < CUSTOMERS; i++)
    for (j = 0; j < CUSTOMERS; j++)
      if (in(j,cross[i]))
	counts[i]++;


  while (nonempty(prods)) {
#ifdef DEBUG
    printf("heuristic11(");
    printbit(PRODUCTS,prods);
    printf(")\n");
    printf("COUNTS:");
    for (j = 0; j < CUSTOMERS; j++)
      printf(" %d", counts[j]);
    printf("\n");
#endif
    /** First just work out the stacks now for each product i in prods **/
    min_now = CUSTOMERS+1;
    cost_now = -CUSTOMERS;
    stacked_after = unionp(prods);
    neg(prods,t1);
    intersect(t1,ALLPRODUCTS,t2);
    stacked_before = unionp(t2);
    for (i = 0; i < PRODUCTS; i++) {
#ifdef DEBUG
      printf("heurloop(%d) i=%d\n",prods,i);
#endif
      /* ignore already played pieces */
      if (!in(i,prods)) continue;
      loopcount++;
      /* update who has arrived */
      union(stacked_before,plays[i],previously_stacked);
      /* previously_stacked = stacked_before | plays[i]; */
      intersect(previously_stacked,stacked_after,stacked_now);
      /* stacked_now = previously_stacked & stacked_after; */
      number_stacks_now = nbitsp(stacked_now);
      if (definite_choice && (subset(plays[i],stacked_before))) {
	/*** an optimal must start with this one **/
#ifdef DEBUG
	printf("DEFINITE CHOICE :");
	printbit(CUSTOMERS,stacked_before);
	printf(" sup ");
	printbit(CUSTOMERS,plays[i]);
	printf("\n");
#endif
	min_i = i;
	min_now = number_stacks_now;
	break;
      }
      removebit(i,prods,t1);
      stacked_strictly_after = unionp(t1);
      neg(stacked_before,t2);
      intersect(plays[i],t2,new_customers);
      intersect(stacked_strictly_after,previously_stacked,t3);
      number_after = nbitsp(t3);
      /* update the counts for each customer */
      for (j = 0; j < CUSTOMERS; j++)
	if (in(j,new_customers))
	  for (k = 0; k <  CUSTOMERS; k++) {
	    if (in(j,cross[k])) counts[k]--;
	    if (!counts[k] && (!in(k,stacked_strictly_after)))
		counts[k] = CUSTOMERS+1; /** customer is finished **/
	  }
      /* find minimum number of neighbours */
      min_cust = CUSTOMERS+1;
      for (j = 0; j < CUSTOMERS; j++)
	if (counts[j] < min_cust) min_cust = counts[j];
      if (min_cust > CUSTOMERS) min_cust = 0;
#ifdef DEBUG
      printf("heuristic11(");
      printbit(PRODUCTS,prods);
      printf(") - i=%d, plays=",i);
      printbit(CUSTOMERS,plays[i]);
      printf(" prev=");
      printbit(CUSTOMERS,previously_stacked);
      printf(" after=");
      printbit(CUSTOMERS,stacked_after);
      printf(" strict_after=");
      printbit(CUSTOMERS,stacked_strictly_after);
      printf(" here=");
      printbit(CUSTOMERS,stacked_now);
      printf(" stacksnow=%d,number_after=%d,mincust=%d\n",
	     number_stacks_now,number_after,min_cust);
      printf("COUNTS:");
      for (j = 0; j < CUSTOMERS; j++)
	printf(" %d", counts[j]);
      printf("\n");
#endif
      /* rest the counts for each customer */
      for (j = 0; j < CUSTOMERS; j++)
	if (in(j,new_customers))
	  for (k = 0; k <  CUSTOMERS; k++) {
	    if (in(j,cross[k]))counts[k]++;
	    if (counts[k] > CUSTOMERS+1) counts[k] = 1;
	  }
      number_stacks_now = max(number_stacks_now,number_after+min_cust);
      if (number_stacks_now < min_now) {
	min_i = i;
	min_now = number_stacks_now;
      }
    }
#ifdef DEBUG
    printf("heuristic(");
    printbit(PRODUCTS,prods);
    printf(") - i=%d, stacksnow=%d, (",min_i,min_now);
    printbit(CUSTOMERS,plays[min_i]);
    printf(")\n");
#endif    
    order[index++] = min_i;
    /** update the counts */
    neg(stacked_before,t1);
    intersect(plays[min_i],t1,new_customers);
    for (j = 0; j < CUSTOMERS; j++)
      if (in(j,new_customers))
	for (k = 0; k <  CUSTOMERS; k++) {
	  if (in(j,cross[k])) counts[k]--;
	  if (!counts[k] && (!in(k,stacked_strictly_after)))
	    counts[k] = CUSTOMERS+1; /** customer is finished **/
	}
#ifdef DEBUG
    printf("COUNTS:");
    for (j = 0; j < CUSTOMERS; j++)
      printf(" %d", counts[j]);
    printf("\n");
#endif
    removebit(min_i,prods,prods);
    min = max(min,min_now);
  }
#ifdef DEBUG
  printf("HEUR(");
  printbit(PRODUCTS,prods);
  printf(") = %d\n",min);
#endif
  return min;
}


/* set up the customer graph */
int customergraph()
{
  int i,j;
    
  for (i = 0; i < PRODUCTS; i++) 
    emptyset(cross[i]);

  for (i = 0; i < PRODUCTS; i++) {
    /* printf("plays %d = ",i);
    printbit(CUSTOMERS,plays[i]);
    printf("\n"); */
    for (j = 0; j < CUSTOMERS; j++) 
      if (in(j,plays[i]))
	union(cross[j],plays[i],cross[j]);
  }

#ifdef DEBUG
  for (i = 0; i < CUSTOMERS; i++) {
    printf("%2d:",i);
    for (j = 0; j < CUSTOMERS; j++) 
      if (in(j,cross[i]))
	printf(" X ");
      else
	printf(" . ");
    printf("\n");
  }
#endif
}

int segment_prods(SET component[MAXPRODUCTS])
{
  int i,j;
  SET seen;
  SET temp;
  SET connected;
  SET cust_comp[CUSTOMERS];
  int components = 0;

  emptyset(seen);
  for (i = 0; i < CUSTOMERS; i++) {
    /* 
    printf("i=%d, cross[i]=");
    printbit(CUSTOMERS,cross[i]);
    printf(", seen=");
    printbit(CUSTOMERS,seen);
    printf("\n");
    */
    if (in(i,seen)) continue;
    emptyset(temp);
    connected = cross[i];
    while (notequal(temp,connected)) {
      temp = connected;
      for (j = 0; j < CUSTOMERS; j++)
	if (in(j,connected))
	  union(connected,cross[j],connected);
    }
    if (intersects(connected,seen)) printf("ERROR: segmenting bug");
    cust_comp[components++] = connected;
    union(seen,connected,seen);
  }
#ifdef DEBUG
  for (i = 0; i < components; i++) {
    printf("CUSTOMER COMPONENT [");
    printbit(CUSTOMERS,cust_comp[i]);
    printf("]\n");
  }
#endif

  for (i = 0; i < components; i++) {
    emptyset(component[i]);
    for (j = 0; j < PRODUCTS; j++)
      if (subset(plays[j],cust_comp[i]))
	addbit(j,component[i],component[i]);
  }
  if (showstats)
    for (i = 0; i < components; i++) {
      printf("PRODUCT COMPONENT [");
      printbit(PRODUCTS,component[i]);
      printf("]\n");
    }
  return components;
}

int lowerb(int current) {
  int i,j;
  SET clique, set;
  SET temp;
  int max;
  SET maxnew;
  int maxj;
  int maxclique = current;
  SET connected;


  for (i = 0; i < PRODUCTS; i++) {
    if (!in(i,ALLPRODUCTS)) continue; 
    universe(clique); 
    set = plays[i];
    for (j = 0; j < CUSTOMERS; j++) 
      if (in(j,plays[i]))
	intersect(clique,cross[j],clique);
#ifdef DEBUG
    printf("prod[i] = %d, clique=%d (",set, clique);
    printbit(CUSTOMERS,set);
    printf(") (");
    printbit(CUSTOMERS,clique);
    printf(")\n");
#endif
    if (nbitsp(clique) <= maxclique) continue;
    while (notequal(clique,set)) {
      /* find bit which when added keeps maximal clique */
#ifdef DEBUG
      printf("prod[i] = %d, clique=%d (",set, clique);
      printbit(CUSTOMERS,set);
      printf(") (");
      printbit(CUSTOMERS,clique);
      printf(")\n");
#endif
      for (j = 0; j < CUSTOMERS; j++) {
	max = 0;
	if (in(j,clique) && !in(j,set)) {
	  intersect(clique,cross[j],temp);
	  /* printf("j=%d, temp=%d\n",j,temp); */
	  if (nbitsp(temp) > max) {
	    maxnew = temp;
	    maxj = j;
	  }
	}
      }
      clique = maxnew;
      if (nbitsp(clique) <= maxclique) break;
      addbit(maxj,set,set);
    }
#ifdef DEBUG
    printf("prod[i] = %d, clique=%d (",set, clique);
    printbit(CUSTOMERS,set);
    printf(") (");
    printbit(CUSTOMERS,clique);
    printf(")\n");
#endif
    if (nbitsp(clique) <= maxclique) continue;
#ifdef DEBUG
    printf("NEW MAX = %d\n",nbitsp(clique));
#endif
    maxclique = nbitsp(clique);
  }

  return maxclique;
}

/* heuristic arc contraction */
int hac(int current) {
  int i,j;
  SET clique, set;
  SET temp;
  int max;
  SET maxnew;
  int maxj;
  int maxclique = current;
  SET connected;
  SET lcross[CUSTOMERS];
  int counts[CUSTOMERS];
  int mindeg, deg;
  int d1,i1,d2,i2;

  for (i = 0; i < CUSTOMERS; i++) 
    emptyset(lcross[i]);

  for (i = 0; i < PRODUCTS; i++) 
     if (in(i,ALLPRODUCTS))
      for (j = 0; j < CUSTOMERS; j++) 
	if (in(j,plays[i]))
	  union(lcross[j],plays[i],lcross[j]);

  emptyset(set);
  mindeg = CUSTOMERS;
  for (i = 0; i < CUSTOMERS; i++) {    
    if (nonempty(lcross[i])) addbit(i,set,set);  /* the set of customers */
    deg = nbitsp(lcross[i]);
    if (deg && deg < mindeg) mindeg = deg;
  }

  current = max(current,mindeg);

  while (1) {
#ifdef DEBUG
    printf("HAC(%d) [",current);
    printbit(CUSTOMERS,set);
    printf("]" );
    for (i = 0; i < CUSTOMERS; i++)
      if (in(i,set)) {
	printbit(CUSTOMERS,lcross[i]);
	printf("(%d) ",i);
      }
    printf("\n");
#endif
    clique = set;
    for (i = 0; i < CUSTOMERS; i++)
      if (in(i,set)) 
	intersect(clique,lcross[i],clique);
    if (equal(clique,set)) { /** clique remains **/
      deg = nbitsp(set);
      return (max(current,deg));
    }
    if (nbitsp(set) <= current) return current;
    d1 = CUSTOMERS;
    for (i = 0; i < CUSTOMERS; i++)
      if (in(i,set))
	if (nbitsp(lcross[i]) < d1) {
	  d1 = nbitsp(lcross[i]);
	  i1 = i;
	}
#ifdef DEBUG
    printf("i1 = %d, d1 = %d\n", i1,d1);
#endif
    if (d1 == 1) /** singleton node **/
      {
	i2 = i1; /* eliminate i2 */
      }
    else {
      d2 = CUSTOMERS;
      for (i = 0; i < CUSTOMERS; i++)
	if ((in(i,set)) && nbitsp(lcross[i]) == d1)
	  for (j = 0; j < CUSTOMERS; j++)
	    if (j != i && in(j,lcross[i]) && nbitsp(lcross[i]) < d2) {
	      i1 = i;
	      i2 = j;
	      d2 = nbitsp(lcross[i]);
	    }
#ifdef DEBUG
      printf("i1 = %d, d1 = %d, i2 = %d, d2 = %d\n",i1,d1,i2,d2);
#endif
      /** merge i1 and i2 **/
      union(lcross[i1],lcross[i2],lcross[i1]);
      /* lcross[i1] = lcross[i1] | lcross[i2]; */
      for (i = 0; i < CUSTOMERS; i++)
	if (in(i,lcross[i1]))
	  addbit(i1,lcross[i],lcross[i]);
    }
    for (i = 0; i < CUSTOMERS; i++)
      removebit(i2,lcross[i],lcross[i]);
    removebit(i2,set,set);

    mindeg = CUSTOMERS;
    for (i = 0; i < CUSTOMERS; i++)  
      if (in(i,set)) {
	deg = nbitsp(lcross[i]);
	if (deg < mindeg) mindeg = deg;
      }

    if (mindeg >= 2) current = max(current,mindeg);
  }

}

int findmin(SET prods, int min, int index) {
  int i;
  SET previously_stacked;
  SET stacked_after;
  SET stacked_now;
  int number_stacks_now;
  SET child;
  SET t1, t2, t3;

  if (empty(prods)) return; /* catch the call for emptyset */
#ifdef DEBUG
  printf("findmin(");
  printbit(PRODUCTS,prods);
  printf(",min=%d,ind=%d)\n",min,index);
#endif
  order[index] = -1;
  for (i = 0; i < PRODUCTS; i++) {
    /* ignore already played pieces */
    if (!in(i,prods)) continue;
    /* if its child was never filled it in its not part of the plan 
       except if its child happens to be 0 */
    removebit(i,prods,child);
#ifdef DEBUG
    printf("findmin(");
    printbit(PRODUCTS,prods);
    printf(")  child=");
    printbit(PRODUCTS,child);
    printf(" ,i=%d,cost=%d)\n",i,hash(child));
#endif
    removebit(i,prods,t1);
    if (!hash(t1) && nonempty(t1)) continue;
    /* update who has stacked */
    neg(prods,t1);
    intersect(t1,ALLPRODUCTS,t2);
    addbit(i,t2,t3);
    previously_stacked = unionp(t3);
    stacked_after = unionp(prods);
    intersect(previously_stacked,stacked_after,stacked_now);
    /* stacked_now = previously_stacked & stacked_after; */
    number_stacks_now = nbitsp(stacked_now);
    if (number_stacks_now > min) continue;
    if (max(number_stacks_now, hash(child)) <= min) {
      order[index] = i;
      removebit(i,prods,t1);
      findmin(t1, min, index+1);
      break;
    }
  }
  if (order[index] < 0) 
    printf("ERROR: no index set prods=%d, min=%d, index=%d\n",prods,min,index);
}

void output(int o[ARRAYPRODUCTS], int pb[ARRAYPRODUCTS][MAXCUSTOMERS], 
	    int PRODS, int CUSTS, char *oname) {
  int i,j,b,minprod,maxprod,s;
  int count[MAXPRODUCTS];


  printf("%s\n",oname);
  for (i = 0; i < PRODS; i++) {
    count[i] = 0;
    printf(" %2d ",o[i]);
  }
  printf("\n");
  for (i = 0; i < PRODS; i++) 
    printf("----");
  printf("\n");
  for (j = 0; j < CUSTS; j++) {
    maxprod = -1;
    for (i = 0; i < PRODS; i++) {
      if (o[i] < 0) continue;
      if (pb[o[i]][j]) maxprod = i;
    }
    minprod = PRODS;
    for (i = 0; i < PRODS; i++) {
      if (o[i] < 0) /** not assigned **/
	printf("  ? ");
      else {
	if (b = pb[o[i]][j]) 
	  minprod = i;
	if (b) {
	  count[i]++;
	  printf("  X ");
	} else if (i > minprod && i < maxprod) {
	  count[i]++;
	  printf("  - ");
	} else
	  printf("  . ");
      }
    }
    printf("\n");
  }
  for (i = 0; i < PRODS; i++) 
    printf("----");
  printf("\n");
  for (i = 0; i < PRODS; i++) {
    printf(" %2d ",count[i]);
  }
  printf("\n");
 
}


readdata(){
  int i,j;
  int tmp;
  long long c;

  scanf("%d",&orig_CUSTOMERS);
  scanf("%d",&orig_PRODUCTS);
  if (orig_CUSTOMERS > MAXCUSTOMERS) {
    printf("ERROR: Too many customers: limit %d\n",MAXCUSTOMERS);
    exit(1);
  }
  if (orig_PRODUCTS > ARRAYPRODUCTS) {
    printf("ERROR: Too many products: limit %d\n",ARRAYPRODUCTS);
    exit(1);
  }
  
  c = 1;
  for (i = 0; i < MAXBIT; i++) {
    bit[i] = c;
    c *= 2;
  }
  

#ifdef DEBUG
  printf("orig_PRODUCTS=%d, orig_CUSTOMERS=%d\n",orig_PRODUCTS,orig_CUSTOMERS);
#endif
  for (i = 0; i < orig_PRODUCTS; i++) 
    emptyset(orig_plays[i]);

  totalcost = 0;
  for (j = 0; j < orig_CUSTOMERS; j++) {
    for (i = 0; i < orig_PRODUCTS; i++) {
      scanf("%d", &tmp);
      orig_playbit[i][j] = tmp;
      if (tmp) addbit(j,orig_plays[i],orig_plays[i]);
    }
  }
#ifdef DEBUG
  for (i = 0; i < orig_PRODUCTS; i++) {
    printf("%d play=%d bits=",i,orig_plays[i]);
    printbit(orig_CUSTOMERS,orig_plays[i]);
    printf("\n");
  }
#endif

  /* set order things to -1 to make print out better for undefined things */
  for (i = 0; i < orig_PRODUCTS; i++) {
    order[i] = -1;
    orig_order[i] = -1;
  }
}

printdata(){
  int i,j;

  printf("c = %d;\n",orig_CUSTOMERS);
  printf("p = %d;\n",orig_PRODUCTS);
  
  printf("orders = [|\n");
  for (j = 0; j < orig_CUSTOMERS; j++) {
    for (i = 0; i < orig_PRODUCTS; i++)
      printf("%d%s", orig_playbit[i][j], (i+1 < orig_PRODUCTS ? ", " : " |"));
    if (j+1 < orig_CUSTOMERS) printf("\n"); else printf("];\n");
  }
}

solve(int indexstart) {
  int min,tmp;
  int i,j;
  int m;
  SET c;
  int upper;
  int l,u;
  int b;
  int maxprod, minprod;
  int mid;
  int cliq,hacb;
  int t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11;
  int save_lowerbound = lowerbound;
  int save_upperbound = upperbound;

  t1 = t2 = t3 = t4 = t5 = t6 = t7 = t8 = t9 = t10 = t11 = CUSTOMERS+1;

  if (showstats) {
    printf("SOLVE(");
    printbit(PRODUCTS,ALLPRODUCTS);
    printf(") = %d\n",indexstart);
  }

  lowerbound = 0;
  for (i = 0; i < PRODUCTS; i++)
    if (in(i,ALLPRODUCTS))
      lowerbound = max(lowerbound,nbitsp(plays[i]));
  if (given_lowerbound > lowerbound) lowerbound = given_lowerbound;

  if (cliquef) {
    cliq = lowerb(lowerbound);
    if (showstats) printf("CLIQUE = %d\n",cliq);
    hacb = hac(lowerbound);
    if (showstats) printf("HAC = %d\n",hacb);
    if (cliq > lowerbound) lowerbound = cliq;
    if (hacb > lowerbound) lowerbound = hacb;
  }

  if (use_heuristic) {
    /*    t1 = heuristic(ALLPRODUCTS,indexstart);
    if (extra_verbose) 
      output(order,playbit,PRODUCTS,CUSTOMERS,"HEURISTIC1");
    t2 = heuristic2(ALLPRODUCTS,indexstart);
    if (extra_verbose)
      output(order,playbit,PRODUCTS,CUSTOMERS,"HEURISTIC2");
    */
    
    t3 = heuristic3(ALLPRODUCTS,indexstart);
    if (extra_verbose)
      output(order,playbit,PRODUCTS,CUSTOMERS,"HEURISTIC3");
    t4 = heuristic4(ALLPRODUCTS,indexstart);
    if (extra_verbose)
      output(order,playbit,PRODUCTS,CUSTOMERS,"HEURISTIC4");

    /* 
    t5 = heuristic5(ALLPRODUCTS,indexstart);
    if (extra_verbose)
      output(order,playbit,PRODUCTS,CUSTOMERS,"HEURISTIC5");
    */
    
    t6 = heuristic6(ALLPRODUCTS,indexstart);
    if (extra_verbose)
      output(order,playbit,PRODUCTS,CUSTOMERS,"HEURISTIC6");
    
    t7 = heuristic7(ALLPRODUCTS,indexstart);
    if (extra_verbose)
      output(order,playbit,PRODUCTS,CUSTOMERS,"HEURISTIC7");

    /* 
    t8 = heuristic8(ALLPRODUCTS,indexstart);
    if (extra_verbose)
      output(order,playbit,PRODUCTS,CUSTOMERS,"HEURISTIC8");
    t9 = heuristic9(ALLPRODUCTS,indexstart);
    if (extra_verbose)
      output(order,playbit,PRODUCTS,CUSTOMERS,"HEURISTIC9");
    */
    
    t10 = heuristic10(ALLPRODUCTS,indexstart);
    if (extra_verbose)
      output(order,playbit,PRODUCTS,CUSTOMERS,"HEURISTIC10"); 
    
    t11 = heuristic11(ALLPRODUCTS,indexstart);
    if (extra_verbose)
      output(order,playbit,PRODUCTS,CUSTOMERS,"HEURISTIC11");
    
    upperbound = minn(t1,minn(t2,minn(t3,minn(t4,minn(t5,minn(t6,minn(t7,minn(t8,minn(t9,minn(t10,t11))))))))));
    
    if (showstats) 
      printf("HEURISTIC %c1=%d, %c2=%d, %c3=%d, %c4=%d, %c5=%d, %c6=%d, %c7=%d, %c8=%d, %c9=%d, %c10=%d, %c11=%d%s\n", 
	     (t1 == upperbound ? '*' : ' '), t1,
	     (t2 == upperbound ? '*' : ' '), t2,
	     (t3 == upperbound ? '*' : ' '), t3,
	     (t4 == upperbound ? '*' : ' '), t4,
	     (t5 == upperbound ? '*' : ' '), t5,
	     (t6 == upperbound ? '*' : ' '), t6,
	     (t7 == upperbound ? '*' : ' '), t7,
	     (t8 == upperbound ? '*' : ' '), t8,
	     (t9 == upperbound ? '*' : ' '), t9,
	     (t10 == upperbound ? '*' : ' '), t10,
	     (t11 == upperbound ? '*' : ' '), t11,
	     "");
    
  }
  else
    upperbound = CUSTOMERS; 
  if (given_upperbound && given_upperbound < upperbound)
    upperbound = given_upperbound;

  if (lowerbound > upperbound) printf("ALERT PROBLEM %s",name);
  if (showstats) printf("lowerbound = %d, upperbound = %d\n",lowerbound,upperbound);
 
  if (stepwise) {
    global_lowerbound = lowerbound;
    global_upperbound = upperbound;
    for (i = global_lowerbound; i <= global_upperbound; i++) {
      lowerbound = upperbound = i;
      if (astar11) min = asmincost11(ALLPRODUCTS);
      else min = asmincost(ALLPRODUCTS);
      if (showstats) printf("STEP (%d) asmin = %d, sets = %d undo=%d [lc=%d,uc=%d,bc=%d,hc=%d,re=%d,dc=%d]\n",i,min,ccc,ucount,loopcount,unioncount,bitscount,hashcount,reuse,definite);
      if (min <= upperbound)
	break;
      undo(faillist);
      faillist = NULL;
    } 
  } 
  else if (backstepwise) {
    global_lowerbound = lowerbound;
    global_upperbound = upperbound;
    for (i = global_upperbound; i >= global_lowerbound; i--) {
      lowerbound = upperbound = i;
      if (astar11) tmp = asmincost11(ALLPRODUCTS);
      else tmp = asmincost(ALLPRODUCTS);
      if (showstats) printf("BACK (%d) asmin = %d, sets = %d undo=%d [lc=%d,uc=%d,bc=%d,hc=%d,re=%d,dc=%d]\n",i,tmp,ccc,ucount,loopcount,unioncount,bitscount,hashcount,reuse,definite);
      if (tmp > upperbound)
	break;
      i = tmp; /** if we found a solution at tmp, then skip down to there **/
      getrusage(RUSAGE_SELF,&optimaltime); 
      optccc = ccc;
      if (verbose) findmin(ALLPRODUCTS,tmp,indexstart);
      /** UNDO the fake bounds **/
      undo(faillist);
      undo(succlist);
      faillist = NULL;
      succlist = NULL;
    }
    min = i+1;
  } else if (binarychop) {
    global_lowerbound = lowerbound;
    global_upperbound = upperbound;
    while (global_lowerbound <= global_upperbound) {
      mid = (global_lowerbound + global_upperbound) / 2;
      lowerbound = upperbound = mid;      
      if (astar11) tmp = asmincost11(ALLPRODUCTS);
      else tmp = asmincost(ALLPRODUCTS);
      if (showstats) printf("CHOP (%d,%d,%d) asmin = %d, sets = %d undo=%d [lc=%d,uc=%d,bc=%d,hc=%d,re=%d,dc=%d]\n",mid,global_lowerbound,global_upperbound,tmp,ccc,ucount,loopcount,unioncount,bitscount,hashcount,reuse,definite);
      if (tmp <= upperbound) {
	min = tmp;
	optccc = ccc;
	getrusage(RUSAGE_SELF,&optimaltime); 
	if (tmp == global_lowerbound) break;/*leave loop without killing cost*/
	global_upperbound = tmp-1;
	if (verbose) findmin(ALLPRODUCTS,min,indexstart);
	undo(faillist);
	undo(succlist);
	faillist = NULL;
	succlist = NULL;
      } else {
	global_lowerbound = mid+1;
	undo(faillist);
	dontundo(succlist);
	faillist = NULL;
	succlist = NULL;
      }
    }
  } else /** once off **/
    {
      if (astar11) min = asmincost11(ALLPRODUCTS);
      else min = asmincost(ALLPRODUCTS);
      if (showstats) printf("ONCE asmin = %d, sets = %d undo=%d [lc=%d,uc=%d,bc=%d,hc=%d,re=%d,dc=%d]\n",min,ccc,ucount,loopcount,unioncount,bitscount,hashcount,reuse,definite);
    }

  if (verbose) {
    if (!binarychop && !backstepwise) findmin(ALLPRODUCTS,min,indexstart);
    if (extra_verbose) 
      output(order,playbit,PRODUCTS,CUSTOMERS,"COMPRESSED ORDER");
  }

  /** restore original bounds **/
  lowerbound = save_lowerbound;
  upperbound = save_upperbound;

  return min;
}

challenge() {
  int min,tmp;
  int i,j;
  int m;
  SET c;
  int upper;
  int l,u;
  int b;
  int maxprod, minprod;
  int mid;
  int cliq, hacb;
  int t1, t2, t3, t4, t5;
  int ncomps;
  SET component[MAXPRODUCTS];
  int indexstart = 0;


  if (use_preprocess) {
    CUSTOMERS = orig_CUSTOMERS;
    PRODUCTS = 0;
    for (i = 0; i < orig_PRODUCTS; i++) {
      rep[i] = i;
      for (j = 0; j < orig_PRODUCTS; j++) {
	if (i == j) continue;
	if (subset(orig_plays[i],orig_plays[j]) 
	    && (notequal(orig_plays[i],orig_plays[j]) || i > j) ) {
	  /* point i at j */
	  /* printf("i=%d, j=%d, oi=%d, oj=%d\n",
	     i,j,orig_plays[i],orig_plays[j]); */
	  rep[i] = j;
	  break;
	}
      }
      if (rep[i] == i) {
	orep[PRODUCTS] = i;
	plays[PRODUCTS] = orig_plays[i];
	for (j = 0; j < orig_CUSTOMERS; j++)
	  playbit[PRODUCTS][j] = orig_playbit[i][j];
	PRODUCTS++;
      }
    }
    if (showstats) printf("PREPROCESS: PRODUCTS = %d\n",PRODUCTS);
   }
  else {
    PRODUCTS = orig_PRODUCTS;
    CUSTOMERS = orig_CUSTOMERS;
    for (i = 0; i < orig_PRODUCTS; i++) {
      plays[i] = orig_plays[i];
      orep[i] = i;
      for (j = 0; j < orig_CUSTOMERS; j++)
	playbit[i][j] = orig_playbit[i][j];
    }
  }  

  if (PRODUCTS > MAXPRODUCTS) {
    printf("ERROR: Too many (non-redundant) products: limit %d\n",MAXPRODUCTS);
    exit(1);
  }
   
  customergraph(); 


    min = 0;
  if (segment) {
    ncomps = segment_prods(component);
    for (i = 0; i < ncomps; i++) {
      /** schedule each segment independently **/
      ALLPRODUCTS = component[i];
      /* printf("i=%d PRODS=[",i);
      printbit(PRODUCTS,ALLPRODUCTS);
      printf("]\n"); */
      tmp = solve(indexstart);
      /*printf("XXXXX min = %d, tmp = %d\n",min,tmp); */
      min = max(min,tmp);
      if (min > lowerbound) lowerbound = min; /* update lowerbound */
      /** start index after the current products **/
      indexstart += nbitsp(component[i]);
    }
  } 
  else {
    emptyset(ALLPRODUCTS);
    for (i = 0; i < PRODUCTS; i++)
      addbit(i,ALLPRODUCTS,ALLPRODUCTS);
    /* printf("i=%d PRODS=[",i);
    printbit(PRODUCTS,ALLPRODUCTS);
    printf("]\n"); */
    min = solve(0);
  }

#ifdef DEBUG
    printf("ORDER: ");
      for (i = 0; i < PRODUCTS; i++)
	printf("%d ",order[i]);
    printf("\n ORIG: ");
      for (i = 0; i < PRODUCTS; i++)
	printf("%d ",orep[order[i]]);
    printf("\n");
#endif
#ifdef MZNO
    printf("objective = %d;\n", min);
    printf("s = [");
    for(i = 0; i < PRODUCTS; i++) {
      printf("%d", order[i]+1);
      if (i+1 < PRODUCTS) printf(", "); else printf("];\n");
    }
#else
  if (verbose) {
    if (use_preprocess) {
      for (i = 0 ; i < orig_PRODUCTS; i++) {
	j = i;
	while (rep[j] != j)
	  j = rep[j];
	rep[i] = j;
      }
      m = 0;
      for (i = 0; i < PRODUCTS; i++) {
	orig_order[m++] = orep[order[i]];
	/*	printf("oo[%d] = %d\n",m-1,orep[order[i]]); */
	for (j = 0; j < orig_PRODUCTS; j++)
	  if (rep[j] != j && rep[j] == orep[order[i]]) {
	    orig_order[m++] = j;
	    /* printf("oo[%d] = %d\n",m-1,j); */
	  }
     }
#ifdef DEBUG
      for (i = 0; i < orig_PRODUCTS; i++)
	printf("i=%d, order=%d, rep =%d\n",i,orig_order[i],rep[i]);
#endif
      output(orig_order,orig_playbit,orig_PRODUCTS,orig_CUSTOMERS,"FINAL");
    } else
      output(order,playbit,PRODUCTS,CUSTOMERS,"FINAL");
  }
#endif  
  return min;
}


main(int argc, char *argv[])
{
  int i;
  char buffer[100];
  char c;
  char flags[100] = ""; 
  int otime, ttime;
  int min;

  for (i = 1; i < argc; i++) {
    strcpy(buffer, argv[i]);
    if (buffer[0] == '-') {
      strcat(flags,buffer+1);
      switch(buffer[1]) {
      case 'h':
	/* heuristic */
	use_heuristic = 1;
	break;
      case 'p':
	/* preprocess */
	use_preprocess = 1;
	break;
      case 'v':
	/* verbose output */
	verbose = 1;
	break;
      case 'a':
	/* astar aalgorithm */
	astar = 1;
	break;
      case 'x':
	/* extra verbose output */
	extra_verbose = 1;
	break;
      case 'l':
	/* lowerbound */
	sscanf(argv[i+1],"%d",&given_lowerbound);
	i++;
	break;
      case 'i':
	/* iteration limit */
	sscanf(argv[i+1],"%d",&LIMIT);
	i++;
	break;
      case 'u':
	/* upperbound */
	sscanf(argv[i+1],"%d",&given_upperbound);
	i++;
	break;
      case 's':
	/* stepwise -- incrementing upper and lower bound */
	stepwise = 1;
	if (backstepwise || binarychop)
	  { printf("ERROR: incompatible flags 'b','w','c'\n"); exit(1); }
	fail_undo = 1;
	break;
      case 'b':
	/* binary chop -- bottom half first */
	binarychop = 1;
	fail_undo = 1;
	succ_undo = 1;
	break;
      case 'c':
	/* clique findign for lower bound */
	cliquef = 1;
	break;
      case 't':
	/* lookahead pruning */
	showstats = 1;
	break;
      case 'n':
	/* lookahead pruning */
	noname = 1;
	break;
      case 'f':
	/* maximise finishes on astar */
	maxfinish = 1;
	break;
      case 'e':
	/* maximise heuristic11 on astar */
	astar11 = 1;
	break;
      case 'g':
	/* segment independent parts */
	segment = 1;
	break;
      case 'd':
	/* definite choice, always place those with subset */
	definite_choice = 1;
	break;
      case 'w':
	/* maximise finishes on astar */
	backstepwise = 1;
	if (stepwise || binarychop)
	  { printf("ERROR: incompatible flags 'b','w' and 'c'\n"); exit(1); }
	fail_undo = 1;
	succ_undo = 1;
	break;
      case 'r':
	/* lookahead pruning */
	sscanf(argv[i+1],"%d",&repeats);
	i++;
      default:
	break;
      }
    }
  }
  if (noname) 
    strcpy(name,"[NONE]\n");
  else
    fgets(name,100,stdin);
  getrusage(RUSAGE_SELF, &starttime);
  readdata();
#ifdef MZN
  printdata();
#else
  min = challenge();
  getrusage(RUSAGE_SELF, &endtime);
  /* timeval_subtract(&endtime,&starttime,&runtime); */
  if (!optccc) optccc = ccc;
  runtime = endtime;
  /* timeval_subtract(&optimaltime,&starttime,&opttime); */
  if (!binarychop && !backstepwise) opttime = endtime;
  else opttime = optimaltime;
  otime = 1000 * opttime.ru_utime.tv_sec + opttime.ru_utime.tv_usec/1000
          + 1000 * opttime.ru_stime.tv_sec + opttime.ru_stime.tv_usec/1000;
  ttime = 1000 * runtime.ru_utime.tv_sec + runtime.ru_utime.tv_usec/1000;
          + 1000 * runtime.ru_stime.tv_sec + runtime.ru_stime.tv_usec/1000;
#ifndef MZNO
  printf("%d %d %d %d %d %d %d %d %s %s", orig_PRODUCTS, orig_CUSTOMERS, 
	 PRODUCTS, min, ccc, optccc, ttime, otime, flags, name);
#endif
#endif
  exit(0);
  
}
