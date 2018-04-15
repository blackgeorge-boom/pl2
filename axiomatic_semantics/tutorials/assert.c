/*@
  @ requires n >= 0 && n < 100;
  */

int f (int n) {

	int tmp = 100 - n;
	//@ assert tmp > 0;
	//@ assert tmp < 100;
	return tmp;

}
