#include <limits.h>

/*@ 
  @ requires n >= 0;
  @ requires \valid (p + (0 .. n - 1));
  @ assigns \nothing;
  @ ensures \result == \sum(0,n−1,\lambda integer i; p[i]*p[i]);
  */

int sqsum (int *p, int n) {

	int s = 0, tmp;
	for (int i = 0; i < n; i++) {
		//@ assert p[i] * p[i] <= INT_MAX;
		tmp = p[i] * p[i];
		//@ assert tmp >= 0; 
		//@ assert tmp + s <= INT_MAX;
		s += tmp;
	}

	return s;
}
