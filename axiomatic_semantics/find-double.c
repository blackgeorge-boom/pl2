#include <stdbool.h> 
#define MAXV 1000000 

/*@
  @ predicate hasDouble{L} (integer N, int *f, integer i) = 
  @		\exists integer j; 0 <= j <= N - 1 && i != j && \at(x[i], L) == \at(x[j], L);
  @*/

/*@
  @ predicate existsDoubleInRange{L} (integer N, int *x, integer i) = 
  @		i >= N ? false :
  @		hasDoubleInRange{L}(N, x, i) ? true   
  @						      		 : hasDouble{L}(N, x, i + 1);
  @*/ 

/*
 * TODO Need to prove that :
 * result != 0 <=> exist a[i], a[j], i != j
 * and a[i] = a[j] = r
 */

/*@ 
  @ requires N >= 1 && N <= 1000000;
  @ requires \valid (f + (0 .. N - 1));
  @ ensures \forall integer i; 0 <= i <= N - 1 ==> f[i] == \old(f[i]);
  @ ensures existsDoubleInRange(N, x, 0) ==> \result == 1;
  @ ensures !(existsDoubleInRange(N, x, 0)) ==> \result == 0;
  @*/
int findDouble(int N, int a[]) { 
	
	bool f[MAXV]; 
	
	for (int i = 1; i <= MAXV; ++i) f[i-1] = false; 
	//@ assert \forall integer i; 0 <= i <= N - 1 ==> f[i] == false;
	
	/*@
	  @ loop invariant 0 <= i <= N;
	  @ loop invariant \forall integer i; 0 <= i <= N ==> !(has
	for (int i = 0; i < N; ++i) 
		if (f[a[i]-1]) return a[i]; 
		else f[a[i]-1] = true; 
	
	return 0;
}
