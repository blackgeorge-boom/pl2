/*@ requires n > 0;
    requires \valid (p + (0 .. n - 1));
    ensures \forall int i; 0 <= i <= n - 1 ==> p[i] == \old(p[i]);
    ensures \forall int i; 0 <= i <= n - 1 ==> \result >= p[i];
	ensures \exists int e; 0 <= e <= n−1 && \result == p[e];
*/

int max_seq(int* p, int n) { 
	
	int res = *p; 

	
	for(int i = 0; i < n; i++) { 
		if (res < *p) { res = *p; } 
		p++; 
	} 
	return res; 
}
/*
int max_seq (int *p, int n) {

	int i;
	int max = p[0];

	for (i = 1; i < n; ++i) {
		if (p[i] > max) max = p[i];
	}	

	return max;
}
*/
