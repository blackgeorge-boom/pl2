#include <stdbool.h> 
#define MAXV 1000000 

/*@
  @ predicate hasDouble{L} (integer N, int *a, integer i) = 
  @		\exists integer j; 0 <= j < N && i != j && \at(a[i], L) == \at(a[j], L);
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
  @ behavior no_double:
  @   assumes \forall integer i; 0 <= i < N ==> !hasDouble(N, a, i);
  @   ensures \result == 0;
  @ behavior not_matches:
  @   assumes \exists integer i; 0 <= i < N && hasDouble(N, a, i);
  @   ensures \exists integer i; 0 <= i < N && hasDouble(N, a, i) && \result == i;
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
int findDouble(int N, int a[]) { 
	
	bool f[MAXV]; 
	// ghost L:
	
	/*@
	  @ loop invariant \let n = MAXV; 1 <= i <= MAXV + 1;
	  @ loop assigns i;
	  @ loop assigns \let n = MAXV; f[0 .. (n - 1)];
	  @*/
	for (int i = 1; i <= MAXV; ++i) {
		f[i-1] = false; 
		//@ assert f[i - 1] == \false;
	}
	
	// loop assigns f[e2];
	
	// ghost int e1 = 0 ;
	// ghost int e2 = 0 ;
	/*@
	  @ loop invariant 0 <= i <= N;
  	  @ loop invariant a[i] >= 1 && a[i] <= 1000000;
	  @ loop invariant \forall integer j; 0 <= j < i ==> !hasDouble(i, a, j);
	  @ loop assigns i;
	  @ loop assigns \let n = MAXV; f[0 .. (n - 1)];
	  @ loop variant N - i;
	  @*/
	for (int i = 0; i < N; ++i) 
		if (f[a[i]-1]) {
			// ghost e1 = a[i];
			return a[i]; 
		}
		else {
			// ghost e2 = a[i] - 1;
			f[a[i]-1] = true; 
		}
	
	return 0;
}
