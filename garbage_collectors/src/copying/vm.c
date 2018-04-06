#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <time.h>

// #define NEXT_INSTRUCTION {printf("0x%x s.top : %d ", *pc, s.top); goto *(void *)(label_tab[*pc]);}
#define NEXT_INSTRUCTION goto *(void *)(label_tab[*pc]);

#define PROGRAM_SIZE 65536

/*
 * In this machine 32-bit signed int, is the same as int.
 * We give 4MB of stack memory. Stack will be an int array.
 * Thus, we define the appropriate stack size:
 * 4MB / 4B = 1048576 integers.
 */

#define STACK_SIZE 1048576

/*
 * Our heap will be split into two spaces, for implementing copying 
 * garbage collection. Each space is represented by an int array.
 */

#define HEAP_SIZE 65536
//#define HEAP_SIZE 2048 

/* Definitions of opcode numbers */

#define HALT  0
#define JUMP  1
#define JNZ   2
#define DUP   3 
#define DROP  4
#define PUSH4 5
#define PUSH2 6
#define PUSH1 7
#define ADD   8
#define SUB   9
#define MUL   10
#define DIV   11
#define MOD   12
#define EQ    13
#define NE    14
#define LT    15
#define GT    16
#define LE    17
#define GE    18
#define NOT   19
#define AND   20
#define OR    21
#define IN    22
#define OUT   23
#define CLOCK 42
#define CONS  43
#define HD    44
#define TL    45



/* Simple stack containing 32-bit signed integers */

struct stack {
    int data[STACK_SIZE];
	char is_root[STACK_SIZE];
    int top;
};

typedef struct stack stack;

stack s;	/* Global stack */

/* Useful stack functions */

void stack_init() {
    s.top = -1;
}

void push(int num) {
    s.data[++s.top] = num;
}

int pop() {
    if (s.top == -1) {
        printf("Stack empty!\n");
        return 0;
    }
  	 
	s.is_root[s.top] = 0;
    return s.data[s.top--];
}

int find(int index) {
	if (s.top - index >= 0)
		return s.data[s.top - index];
	else {
		printf("Stack too small!\n");
		return 0;
	}
}




/* Simple heap containing 32-bit signed integers */

struct heap {
	
	/*
	 * Cons cells will be stored in data[]. If head is stored
	 * at data[i], then tail will be stored at data[i + 1].
	 */
	int data[HEAP_SIZE];

	/*
	 * If is_pointer[index] is set to 1, it means that data[index]
	 * points somewhere to the heap.
	 */
	char is_pointer[HEAP_SIZE];

	/*
	 * If the value of an element is 1, it means that the element
	 * is a pointer that has been forwarded and points to to-space. 
	 * Else it points to from-space, and needs to be forwarded.
	 */
	char forwarded[HEAP_SIZE];

	/*
	 * If heap is used as from-space, scan will always be zero.
	 * If heap is used as to-space, scan is used for 
	 * Cheney's algorithm implementation.
	 */
	int scan;

	/*
	 * If heap is used as from-space, next will point to the next
	 * available memory slot. If heap is used as to-space, next is used for 
	 * Cheney's algorithm implementation.
	 */
	int next;
};	

typedef struct heap heap;

heap heap1, heap2; 	/* The two heaps will be used interchangeably for copying GC */

/* 
 * If reversed is false, heap1 is from-space and heap2 is to-space.
 * If reversed is set, heaps are swapped.
 */
int reversed = 0; 	

/* Useful heap functions */

void heap_init (heap *h) { 
	int i;
	
	h->scan = 0;
	h->next = 0;

	for (i = 0; i < HEAP_SIZE; i++) {
		h->is_pointer[i] = 0;
		h->forwarded[i] = 0;
	}
}

int store (heap *h, int a, int b) {

	int index = h->next;
	h->data[index] = a;
	h->data[index + 1] = b;
	h->next += 2;
	//printf("Storing at : %d\n", index);

	return index;
}

int retrieve_head (heap *h, int index) {

	//print_heap(h);
	if (index >= 0 && index < HEAP_SIZE - 1) {
		//printf("Retrieving head %d from : %d\n", h->data[index], index);
		return h->data[index];
	}
	else {
	 	printf("Illegal heap access from retrieve_head\n");
		return 0;	
	}
}

int retrieve_tail (heap *h, int index) {

	//print_heap(h);
	if (index >= 0 && index < HEAP_SIZE - 1) {
		//printf("Retrieving tail %d from : %d\n", h->data[index + 1], index);
		return h->data[index + 1];
	}
	else {
		printf("Illegal heap access from retrieve_tail\n");
		return 0;
	}
}

void print_heap (heap *h) {
	int i;
	printf("Heap : ");
	for (i = h->scan ; i < h->next ; i++) printf("%d ", h->data[i]);
	printf("\n");
}




/* Useful functions for parsing bytecode */

int get_byte (unsigned char *buff) {
	int result;
	//printf("byte_signed %d\n", buff[0]);
	result = buff[0];
	return result;
}

int get_2_bytes (unsigned char *buff) {
	int result;
	//printf("2_byte_signed %d %d\n", buff[0], buff[1]);
	result = buff[0] | buff[1] << 8;
	return result;
}

int get_4_bytes (unsigned char *buff) {
	int result;
	//printf("4_byte_signed %d %d %d %d\n", buff[0], buff[1], buff[2], buff[3]);
	result = buff[0] | buff[1] << 8 | buff[2] << 16 | buff[3] << 24;
	return result;
}




/* Read byte program from file and return in to an array */

int read_program (char *filename, char *buffer) {

	FILE *fileptr;
	long file_len = 0;
	char c;

	fileptr = fopen(filename, "r");

	/* 
	 * Scan one byte at a time, till
	 * you reach the end of file.
	 */

	while (fscanf(fileptr, "%c", &c) != EOF) {
		buffer[file_len++] = c;
		printf("%04x ", c);
	} 

	printf("\n");

	fclose(fileptr);

    return file_len;
}


int forward (int index) {

	int i;

	/* Check which heap is from-space */
	if (!reversed) {

		if (!heap1.forwarded[index]) {

			/* If the record has not been copied, copy the two fields (head and tail) */
			for (i = 0; i < 2; i++) {

				heap2.data[heap2.next + i] = heap1.data[index + i];
				if (heap1.is_pointer[index + i]) heap2.is_pointer[heap2.next + i] = 1;
			}
				
				/* Head now points to the new copy in to-space */
				heap1.data[index] = heap2.next;
				heap1.forwarded[index] = 1;

				heap2.next += 2;

		}

		/* Return the address of the newly copied record. */
		return heap1.data[index];

	}
	else {	/* Same as before with heaps reversed */ 	
		
		if (!heap2.forwarded[index]) {

			for (i = 0; i < 2; i++) {

				heap1.data[heap1.next + i] = heap2.data[index + i];
				if (heap2.is_pointer[index + i]) heap1.is_pointer[heap1.next + i] = 1;
			}

				heap2.data[index] = heap1.next;
				heap2.forwarded[index] = 1;

				heap1.next += 2;

		}
		
		return heap2.data[index];

	}

}

void cheney () {

	int i;

	/* Check which heap is from-space */
	if (!reversed) {

		heap_init(&heap2);

		/* Forward all roots */
		for (i = 0; i <= s.top; i++) 
			if (s.is_root[i]) s.data[i] = forward(s.data[i]);

		/* Forward all the pointers in to-space */
		while (heap2.scan < heap2.next) {
			
			if (heap2.is_pointer[heap2.scan]) 
				heap2.data[heap2.scan] = forward(heap2.data[heap2.scan]);
			heap2.scan++;
			
		}

	}
	else { /* Same as before with heaps reversed */ 	

		heap_init(&heap1);

		for (i = 0; i <= s.top; i++) 
			if (s.is_root[i]) forward(s.data[i]);

		while (heap1.scan < heap1.next) {
			
			if (heap1.is_pointer[heap1.scan]) 
				heap1.data[heap1.scan] = forward(heap1.data[heap1.scan]);
			heap1.scan++;
			
		}

	}
	
	return;
}


int main (int argc, char const *argv[])
{
    char byte_program[PROGRAM_SIZE], *pc;
    short int opcode;
    int i, prog_len, data, data1, data2;
	unsigned int jump_addr, index;

	double time_spent;
	clock_t begin, end;
	char flag1, flag2;

	/*
	 * Interpreter will be indirectly threaded, so we need
	 * a table of labels to guide us to the next instruction.
	 * Each instruction is mapped to a cell in the table, using 
	 * the op code as index.
	 * Bogus labels are used to preserve mapping for the clock,
	 * cons, hd and tl bytecode instructions.
	 */

	static void *label_tab[] = {

		&&halt_label,
		&&jump_label,
		&&jnz_label,
		&&dup_label,
		&&drop_label,
		&&push4_label,
		&&push2_label,
		&&push1_label,
		&&add_label,
		&&sub_label,
		&&mul_label,
		&&div_label,
		&&mod_label,
		&&eq_label,
		&&ne_label,
		&&lt_label,
		&&gt_label,
		&&le_label,
		&&ge_label,
		&&not_label,
		&&and_label,
		&&or_label,
		&&in_label,
		&&out_label,
		&&bogus_label,
		&&bogus_label,
		&&bogus_label,
		&&bogus_label,
		&&bogus_label,
		&&bogus_label,
		&&bogus_label,
		&&bogus_label,
		&&bogus_label,
		&&bogus_label,
		&&bogus_label,
		&&bogus_label,
		&&bogus_label,
		&&bogus_label,
		&&bogus_label,
		&&bogus_label,
		&&bogus_label,	
		&&bogus_label,
		&&clock_label,
		&&cons_label,
		&&hd_label,
		&&tl_label

	};
    
	stack_init();
	heap_init(&heap1);
	heap_init(&heap2);

	/* Read the bytecode */
	printf("Bytecode read : \n");
    prog_len = read_program(argv[1], byte_program);
	printf("\n");

    pc = &byte_program[0];

    while(1) {

        next_instruction:
		begin = clock();
        opcode = pc[0];
        switch (opcode) {

			case HALT:
			halt_label:
				//printf("halt\n");
				//print_heap(&heap1);
				//print_heap(&heap2);
				goto out;

			case JUMP:
			jump_label:
				//printf("jump ");
				jump_addr = get_2_bytes(&pc[1]);
				//printf("%d\n", jump_addr);
				pc = &byte_program[jump_addr];
				NEXT_INSTRUCTION;

			case JNZ:
			jnz_label:
				//printf("jnz ");
				data = pop();
				if (data != 0) {
					jump_addr = get_2_bytes(&pc[1]);
					//printf("%d\n", jump_addr);
					pc = &byte_program[jump_addr];
				}
				else {
					pc += 3;
					//printf("\n");
				}
				NEXT_INSTRUCTION;

			case DUP:
			dup_label:
				//printf("dup ");
				index = get_byte(&pc[1]);
				//printf("%d\n", index);
				data = find(index);
				push(data);
				if (s.is_root[index]) s.is_root[s.top] = 1;
				pc += 2;	
				NEXT_INSTRUCTION;

			case DROP:
			drop_label:
				//printf("drop\n");
				data = pop();
				pc += 1;
				NEXT_INSTRUCTION;

			case PUSH4:
			push4_label:
				//printf("push4 ");
				data = get_4_bytes(&pc[1]);
				//printf("%d\n", data);
				push(data);
				pc += 5;
				NEXT_INSTRUCTION;	
				
			case PUSH2:
			push2_label:
				//printf("push2 ");
				data = get_2_bytes(&pc[1]);
				//printf("%d\n", data);
				push(data);
				pc += 3;
				NEXT_INSTRUCTION;	
				
			case PUSH1:
			push1_label:
				//printf("push1 ");
				data = get_byte(&pc[1]);
				//printf("%d\n", data);
				push(data);
				pc += 2;
				NEXT_INSTRUCTION;	

			case ADD:
			add_label:
				//printf("add\n");
				data1 = pop();
				data2 = pop();
				push(data1 + data2);
				pc += 1;
				NEXT_INSTRUCTION;

			case SUB:
			sub_label:
				//printf("sub\n");
				data1 = pop();
				data2 = pop();
				push(data2 - data1);
				pc += 1;
				NEXT_INSTRUCTION;
	
			case MUL:
			mul_label:
				//printf("mul\n");
				data1 = pop();
				data2 = pop();
				push(data1 * data2);
				pc += 1;
				NEXT_INSTRUCTION;

			case DIV:
			div_label:
				//printf("div\n");
				data1 = pop();
				data2 = pop();
				push(data2 / data1);
				pc += 1;
				NEXT_INSTRUCTION;

			case MOD:
			mod_label:
				//printf("mod\n");
				data1 = pop();
				data2 = pop();
				push(data2 % data1);
				pc += 1;
				NEXT_INSTRUCTION;

			case EQ:
			eq_label:
				//printf("eq\n");
				data1 = pop();
				data2 = pop();
				push(data1 == data2);
				pc += 1;
				NEXT_INSTRUCTION;

			case NE:
			ne_label:
				//printf("ne\n");
				data1 = pop();
				data2 = pop();
				push(data1 != data2);
				pc += 1;
				NEXT_INSTRUCTION;

			case LT:
			lt_label:
				//printf("lt\n");
				data1 = pop();
				data2 = pop();
				push(data2 < data1);
				pc += 1;
				NEXT_INSTRUCTION;
			
			case GT:
			gt_label:
				//printf("gt\n");
				data1 = pop();
				data2 = pop();
				push(data2 > data1);
				pc += 1;
				NEXT_INSTRUCTION;
			
			case LE:
			le_label:
				//printf("le\n");
				data1 = pop();
				data2 = pop();
				push(data2 <= data1);
				pc += 1;
				NEXT_INSTRUCTION;
			
			case GE:
			ge_label:
				//printf("ge\n");
				data1 = pop();
				data2 = pop();
				push(data2 >= data1);
				pc += 1;
				NEXT_INSTRUCTION;
			
			case NOT:
			not_label:
				//printf("not\n");
				data = pop();
				push(data == 0);
				pc += 1;
				NEXT_INSTRUCTION; 

			case AND: 
			and_label:
				//printf("and\n");
				data1 = pop();
				data2 = pop();
				push(data1 != 0 && data2 != 0);
				pc += 1;
				NEXT_INSTRUCTION;
				
			case OR: 
			or_label:
				//printf("or\n");
				data1 = pop();
				data2 = pop();
				push(data1 != 0 || data2 != 0);
				pc += 1;
				NEXT_INSTRUCTION;

			case IN:
			in_label:
				//printf("in\n");
				scanf("%c", data);
				push(data);
				pc += 1;
				NEXT_INSTRUCTION;

			case OUT:
			out_label:
				//printf("out\n");
				data = pop();
				printf("%c", data);
				pc += 1;
				NEXT_INSTRUCTION;
		   
			case CLOCK:
			clock_label:
				//printf("clock\n");
				end = clock();
				time_spent = (double)(end - begin) / CLOCKS_PER_SEC;
				printf("%0.6lf\n", time_spent);	
				pc += 1;
				NEXT_INSTRUCTION;
				
			case CONS:
			cons_label:
				//printf("cons\n");

				if (s.is_root[s.top]) {printf(""); flag1 = 1;}
				data1 = pop();
				if (s.is_root[s.top]) {printf(""); flag2 = 1;}
				data2 = pop();

				if (!reversed) index = heap1.next;
				else index = heap2.next;

				if (index >= HEAP_SIZE - 1) {

					printf("Initiating garbage collection. Index is : %d\n", index);
					cheney();
					reversed = !reversed;
					printf("reversed : %d\n", reversed);

				}
				
				if (!reversed) {

					index = store(&heap1, data2, data1);
					if (flag2) heap1.is_pointer[index] = 1;
					if (flag1) heap1.is_pointer[index + 1] = 1;

				}	
				else {

					index = store(&heap2, data2, data1);
					//printf("index is : %d\n", index);
					if (flag2) heap2.is_pointer[index] = 1;
					if (flag1) heap2.is_pointer[index + 1] = 1;

				}

				flag1 = 0;
				flag2 = 0;

				push(index);
				s.is_root[s.top] = 1;

				pc += 1;
				NEXT_INSTRUCTION;

			case HD:
			hd_label:
				//printf("hd\n");
				index = pop();

				if (!reversed) {
					data = retrieve_head(&heap1, index);
					if (heap1.is_pointer[index]) flag1 = 1;
				}
				else {
					data = retrieve_head(&heap2, index); 
					if (heap2.is_pointer[index]) flag1 = 1;
				}

				push(data);
				if (flag1) s.is_root[s.top] = 1;

				flag1 = 0;
				pc += 1;
				NEXT_INSTRUCTION;

			case TL:
			tl_label:
				//printf("tl\n");
				index = pop();
				
				if (!reversed) {
					data = retrieve_tail(&heap1, index);
					if (heap1.is_pointer[index + 1]) flag1 = 1;
				}
				else {
					data = retrieve_tail(&heap2, index); 
					if (heap2.is_pointer[index + 1]) flag1 = 1;
				}

				push(data);
				if (flag1) s.is_root[s.top] = 1;
				
				flag1 = 0;
				pc += 1;
				NEXT_INSTRUCTION;
        }

    }

bogus_label:

out:	
    return 0;

}
