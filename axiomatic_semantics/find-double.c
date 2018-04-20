#include <stdbool.h> 
#define MAXV 1000000 

/*@
  @ predicate hasDouble{L} (integer N, int *a, integer i) = 
  @		\exists integer j; 0 <= j <= N && i != j && \at(a[i], L) == \at(a[j], L);
  @*/

/*@
  @ predicate existsDoubleInRange{L} (integer N, int *a, integer i) = 
  @		i >= N ? \false :
  @		hasDouble{L}(N, a, i) ? \true   
  @				       		  : hasDouble{L}(N, a, i + 1);
  @*/ 

/*
 * TODO Need to prove that :
 * result != 0 <=> exist a[i], a[j], i != j
 * and a[i] = a[j] = r
 */

/*@ 
  @ requires N >= 1 && N <= 1000000;
  @ requires \valid (a + (0 .. N - 1));
  @ requires \forall integer i; 0 <= i < N ==> a[i] >= 1 && a[i] <= 1000000;
  @ ensures \forall integer i; 0 <= i < N ==> a[i] == \old(a[i]);
  @ ensures existsDoubleInRange(N, a, 0) ? \result != 0 : \result == 0;
  @*/
int findDouble(int N, int a[]) { 
	
	bool f[MAXV]; 
	//@ ghost L:
	
	/*@
	  @ loop invariant 1 <= i <= MAXV + 1;
	  @ loop assigns i, f[0 .. (MAXV - 1)];
	  @*/
	for (int i = 1; i <= MAXV; ++i) {
		f[i-1] = false; 
		//@ assert f[i - 1] == \false;
	}
	
	// loop assigns f[e2];
	
	//@ ghost int e1 = 1 ;
	//@ ghost int e2 = 0 ;
	/*@
	  @ loop invariant 0 <= i <= N;
	  @ loop invariant i == 0 ==> !(existsDoubleInRange(i, a, 0));
	  @ loop invariant i > 0 ==> !(existsDoubleInRange(i - 1, a, 0));
  	  @ loop invariant \forall integer i; 0 <= i < N ==> a[i] >= 1 && a[i] <= 1000000;
	  @ loop invariant 1 <= e1 <= MAXV;
	  @ loop invariant 0 <= e2 <= MAXV - 1;
	  @ loop variant N - i;
	  @*/
	for (int i = 0; i < N; ++i) 
		if (f[a[i]-1]) {
			//@ ghost e1 = a[i];
			return a[i]; 
		}
		else {
			//@ ghost e2 = a[i] - 1;
			f[a[i]-1] = true; 
		}
	
	return 0;
}
