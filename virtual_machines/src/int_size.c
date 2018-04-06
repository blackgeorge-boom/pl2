#include <stdio.h>
#include <limits.h>
#include <time.h>
#include <unistd.h>

int main() {

   clock_t begin = clock();
   printf("Storage size for int : %d \n", sizeof(int));
   printf("Storage size for char : %d \n", sizeof(char));
   printf("Storage size for long: %d \n", sizeof(long int));
   printf("Storage size for long long : %d \n", sizeof(long long int));
   printf("Storage size for float : %d \n", sizeof(float));
   printf("Storage size for double : %d \n", sizeof(double));
   printf("int > char ? : %d\n",sizeof(int) > sizeof(char));		
   printf("int <= char ? : %d\n",sizeof(int) <= sizeof(char));		 
   clock_t end = clock();
   double time_spent = (double)(end - begin) / CLOCKS_PER_SEC;
   printf("Execution Time : %0.6lf\n", time_spent);
   return 0;
}
