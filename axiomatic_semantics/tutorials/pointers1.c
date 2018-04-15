/*@ requires \valid(p) && \valid(q);
    ensures *p <= *q;
 */

void max_ptr (int *p, int *q) {

	if (*p > *q) {
		int tmp = *p;
		*p = *q;
		*q = tmp;
	}
}
