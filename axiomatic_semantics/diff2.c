#include <stdbool.h> 
#define MAXV 1000000 

/*@ 
  @ requires 1 <= N;
  @ requires \valid (a + (0 .. N - 1));
  @ requires \forall integer i; 0 <= i < N ==> 1 <= a[i] <= MAXV;
  @ ensures \result != 0 <==> \exists integer i, j; 0 <= i < j < N && a[i] == a[j] == \result;
  @*/
int findDouble(int N, int a[]) { 
	
	bool f[MAXV]; 
	
	/*@
	  @ loop invariant \let n = MAXV; 1 <= i <= n + 1;
	  @ loop invariant \forall integer k; 1 <= k < i ==> f[k-1] == false;
	  @ loop assigns i, f[0 .. (i - 1)];
	  @ loop variant \let n = MAXV; n-i;
	  @*/
	for (int i = 1; i <= MAXV; ++i) f[i-1] = false; 
	
	/*@
	  @ loop invariant 0 <= i <= N;
	  @ loop invariant \let n = MAXV; \forall integer k; 1 <= k <= n ==>
	  @   (f[k-1] <==> \exists integer j; 0 <= j < i && a[j] == k);
	  @ loop assigns i; 
	  @ loop assigns f[..]; 
	  @ loop variant N - i;
	  @*/
	for (int i = 0; i < N; i++) if (f[a[i]-1]) return a[i]; else f[a[i]-1] = true; 

	return 0;
}
