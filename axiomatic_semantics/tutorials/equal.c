int equal(int *a, int n, int* b) { 
	
	/*@ 
	  @ loop invariant 0 <= i <= n; 
	  @ loop invariant \forall integer k; 0 <= k < i ==> a[k] == b[k]; 
	  @ loop assigns i; 
	  @ loop variant n-i; 
	  @*/ 
	for (int i = 0; i < n; i++) { 
		if (a[i] != b[i]) { 
			return 0; 
		} 
	} return 1; 
}
