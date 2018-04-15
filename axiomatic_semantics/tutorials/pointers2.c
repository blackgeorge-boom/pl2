/*@ requires \valid(p) && \valid(q);
    ensures *p <= *q;
	ensures (*p == \old(*p) && *q == \old(*q)) ||
			(*p == \old(*q) && *q == \old(*p)); 
 */

void max_ptr (int *p, int *q) {

	if (*p > *q) {
		int tmp = *p;
		*p = *q;
		*q = tmp;
	}
}
