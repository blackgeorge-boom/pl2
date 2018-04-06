all: vm debug_vm int_size mas
	
default: mas 

vm: vm.c
	gcc -Wall -o vm vm.c
debug_vm: debug_vm.c
	gcc -Wall -o debug_vm debug_vm.c
int_size: int_size.c
	gcc -Wall -o int_size int_size.c
mas: mas.c
	gcc -Wall -o mas mas.c
clean: 
	rm *.o int_size vm debug_vm mas
