/*@
  @	logic integer fact (integer n) = 
  @ 	(n > 0) ? n * fact(n - 1)
  @ 			: 1;
  @*/ 

/*@
  @ requires n > 0;
  @ ensures \result == fact(n);
  @*/ 

int fact (int n) {

	int p = 1;
	int i = 2;

	/*@
	  @ loop invariant 2 <= i;
	  @ loop invariant n == 0 ==> p == 1;
	  @ loop invariant n > 0 ==> i <= n + 1 && p == fact (i - 1);
	  @ loop assigns p, i;
	  @ loop variant n - i;
	  @*/ 
	while (i <= n) {
		p = p * i;
		i++;
	}

	return p;
}

