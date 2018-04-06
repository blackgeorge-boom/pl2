/*
 * Nikos Mavrogeorgis 03113087
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <time.h>

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
 * We give 1MB of heap memory. Heap will be an int array.
 * Thus, we define the appropriate heap size:
 * 1MB / 4B = 262144 integers.
 */

#define HEAP_SIZE 262144

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
	 * is a pointer that has been marked. 
	 */
	char marked[HEAP_SIZE];

};	

typedef struct heap heap;

heap *h; 	/* Pointer to global heap */

/* Useful heap functions */

void store (int index, int a, int b) {

	h->data[index] = a;
	h->data[index + 1] = b;
	return;

}

int retrieve_head (int index) {

	if (index >= 0 && index < HEAP_SIZE - 1) {
		return h->data[index];
	}
	else {
	 	printf("Illegal heap access from retrieve_head\n");
		return 0;	
	}
}

int retrieve_tail (int index) {

	if (index >= 0 && index < HEAP_SIZE - 1) {
		return h->data[index + 1];
	}
	else {
		printf("Illegal heap access from retrieve_tail\n");
		return 0;
	}
}

void print_heap () {
	
	int i;
	printf("Heap : ");
	for (i = 0; i < HEAP_SIZE; i++) printf("%d ", h->data[i]);
	printf("\n");
	
}




/* Free list structure */

struct node {

	/* Pointer to a free block in the heap */
	int index;

	/* 
	 * Capacity of the free block. Initial block has capacity 65536.
	 * All the next blocks will have capacity 2 (a whole cons cell)
	 */
	int capacity;

	/* Pointer to the next block */ 
	struct node *next;
	
};

typedef struct node *list_ptr;

/* 
 * Initialize global free list. The first node created
 * will represent the entire heap. As heap is allocated, the 
 * node will get smaller and smaller until depleted.
 * Then mark-and-sweep will take place, and it will add to the list
 * small nodes as big as a cons cell. From this point, only small nodes 
 * will be available in the free list.
 */

list_ptr free_list;

/*
 * Returns an index to the first available block in heap.
 * If there is not enough heap memory, returns an error.
 */

void heap_init () { 
	
	int i;

	free_list = malloc(sizeof(struct node));
	free_list->index = 0;
	free_list->capacity = HEAP_SIZE;
	free_list->next = NULL;

	h = malloc(sizeof(heap));

	for (i = 0; i < HEAP_SIZE; i++) {
		h->is_pointer[i] = 0;
		h->marked[i] = 0;
	}
}

int heap_alloc () {

	int index = -1;

	/* If heap memory is depleted, call mark and sweep */
	if (free_list == NULL) {			
		
		mark_and_sweep(); 
		
	}

	/* If there is still no memory, return -1 (error index) */

	if (free_list == NULL) return -1;			
	
	/* Return a pointer to the first available block */

	index = free_list->index;

	/* 
	 * Shrink memory block. The first big block is shrunk 
	 * multiple times. After garbage collection, small blocks 
	 * are shrunk only once, and then they get depleted.
	 */

	free_list->index += 2;
	free_list->capacity -= 2;

	/* Remove the node from free_list if it is depleted */

	if (free_list->capacity == 0) {	

		list_ptr t = free_list;
		free_list = free_list->next;
		free(t);

	}

	return index;
}

/*
 * Inserts a block to free_list, if it was a garbage.
 */

void heap_free (int index) {

	list_ptr t = malloc(sizeof(struct node));

	t->index = index;
	t->capacity = 2;
	t->next = free_list;

	free_list = t;

	return;
}
	
/* Mark all reachable nodes by a pointer using Depth First Search */

void dfs (int index) {

	if (!h->marked[index]) {

		h->marked[index] = 1;

		if (h->is_pointer[index]) dfs(h->data[index]);
		if (h->is_pointer[index + 1]) dfs(h->data[index + 1]);
	}
	
	return;
}

/* Mark and Sweep algorithm implementation */

void mark_and_sweep () {

	int i = 0;
	
	/* Mark phase */

	for (i = 0; i <= s.top; ++i) 
		if (s.is_root[i]) dfs(s.data[i]);

	/* Sweep phase */

	int p = 0;	/* First address in heap */

	while (p < HEAP_SIZE) {

		if (h->marked[p]) h->marked[p] = 0;
		else heap_free(p);

		p += 2;
	}

	return;
}

/* Useful functions for parsing bytecode */

int get_byte (unsigned char *buff) {
	int result;
	result = buff[0];
	return result;
}

int get_2_bytes (unsigned char *buff) {
	int result;
	result = buff[0] | buff[1] << 8;
	return result;
}

int get_4_bytes (unsigned char *buff) {
	int result;
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
		//printf("%04x ", c);
	} 

	//printf("\n");

	fclose(fileptr);

    return file_len;
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
	heap_init();

	/* Read the bytecode */
    prog_len = read_program(argv[1], byte_program);

    pc = &byte_program[0];

    while(1) {

        next_instruction:
		begin = clock();
        opcode = pc[0];
        switch (opcode) {

			case HALT:
			halt_label:
				goto out;

			case JUMP:
			jump_label:
				jump_addr = get_2_bytes(&pc[1]);
				pc = &byte_program[jump_addr];
				NEXT_INSTRUCTION;

			case JNZ:
			jnz_label:
				data = pop();
				if (data != 0) {
					jump_addr = get_2_bytes(&pc[1]);
					pc = &byte_program[jump_addr];
				}
				else {
					pc += 3;
				}
				NEXT_INSTRUCTION;

			case DUP:
			dup_label:
				index = get_byte(&pc[1]);
				data = find(index);
				push(data);
				if (s.is_root[index]) s.is_root[s.top] = 1;
				pc += 2;	
				NEXT_INSTRUCTION;

			case DROP:
			drop_label:
				data = pop();
				pc += 1;
				NEXT_INSTRUCTION;

			case PUSH4:
			push4_label:
				data = get_4_bytes(&pc[1]);
				push(data);
				pc += 5;
				NEXT_INSTRUCTION;	
				
			case PUSH2:
			push2_label:
				data = get_2_bytes(&pc[1]);
				push(data);
				pc += 3;
				NEXT_INSTRUCTION;	
				
			case PUSH1:
			push1_label:
				data = get_byte(&pc[1]);
				push(data);
				pc += 2;
				NEXT_INSTRUCTION;	

			case ADD:
			add_label:
				data1 = pop();
				data2 = pop();
				push(data1 + data2);
				pc += 1;
				NEXT_INSTRUCTION;

			case SUB:
			sub_label:
				data1 = pop();
				data2 = pop();
				push(data2 - data1);
				pc += 1;
				NEXT_INSTRUCTION;
	
			case MUL:
			mul_label:
				data1 = pop();
				data2 = pop();
				push(data1 * data2);
				pc += 1;
				NEXT_INSTRUCTION;

			case DIV:
			div_label:
				data1 = pop();
				data2 = pop();
				push(data2 / data1);
				pc += 1;
				NEXT_INSTRUCTION;

			case MOD:
			mod_label:
				data1 = pop();
				data2 = pop();
				push(data2 % data1);
				pc += 1;
				NEXT_INSTRUCTION;

			case EQ:
			eq_label:
				data1 = pop();
				data2 = pop();
				push(data1 == data2);
				pc += 1;
				NEXT_INSTRUCTION;

			case NE:
			ne_label:
				data1 = pop();
				data2 = pop();
				push(data1 != data2);
				pc += 1;
				NEXT_INSTRUCTION;

			case LT:
			lt_label:
				data1 = pop();
				data2 = pop();
				push(data2 < data1);
				pc += 1;
				NEXT_INSTRUCTION;
			
			case GT:
			gt_label:
				data1 = pop();
				data2 = pop();
				push(data2 > data1);
				pc += 1;
				NEXT_INSTRUCTION;
			
			case LE:
			le_label:
				data1 = pop();
				data2 = pop();
				push(data2 <= data1);
				pc += 1;
				NEXT_INSTRUCTION;
			
			case GE:
			ge_label:
				data1 = pop();
				data2 = pop();
				push(data2 >= data1);
				pc += 1;
				NEXT_INSTRUCTION;
			
			case NOT:
			not_label:
				data = pop();
				push(data == 0);
				pc += 1;
				NEXT_INSTRUCTION; 

			case AND: 
			and_label:
				data1 = pop();
				data2 = pop();
				push(data1 != 0 && data2 != 0);
				pc += 1;
				NEXT_INSTRUCTION;
				
			case OR: 
			or_label:
				data1 = pop();
				data2 = pop();
				push(data1 != 0 || data2 != 0);
				pc += 1;
				NEXT_INSTRUCTION;

			case IN:
			in_label:
				scanf("%c", data);
				push(data);
				pc += 1;
				NEXT_INSTRUCTION;

			case OUT:
			out_label:
				data = pop();
				printf("%c", data);
				pc += 1;
				NEXT_INSTRUCTION;
		   
			case CLOCK:
			clock_label:
				end = clock();
				time_spent = (double)(end - begin) / CLOCKS_PER_SEC;
				printf("%0.6lf\n", time_spent);	
				pc += 1;
				NEXT_INSTRUCTION;
				
			case CONS:
			cons_label:

				/* 
				 * Pop tail. Pop head.
				 * Check if the elements to be stored were pointers to the heap 
				 */

				if (s.is_root[s.top]) flag1 = 1;
				data1 = pop();
				if (s.is_root[s.top]) flag2 = 1;
				data2 = pop();

				/* Request memory for cons cell */
				
				index = heap_alloc();
				if (index == -1) {printf("Out of memory error\n"); goto out;}

				/* Store the cons cell. Check if elements were pointers */

				store(index, data2, data1);
				if (flag2) h->is_pointer[index] = 1;
				if (flag1) h->is_pointer[index + 1] = 1;

				/* Reset flags */

				flag1 = 0;
				flag2 = 0;

				/* The returned address is pushed to the stack and is a pointer */

				push(index);
				s.is_root[s.top] = 1;

				pc += 1;
				NEXT_INSTRUCTION;

			case HD:
			hd_label:

				/* Fetch heap adress */
				
				index = pop();

				/* Retrieve head and see if it was a pointer */

				data = retrieve_head(index);
				if (h->is_pointer[index]) flag1 = 1;

				push(data);
				if (flag1) s.is_root[s.top] = 1;

				/* Reset flag */

				flag1 = 0;
				pc += 1;
				NEXT_INSTRUCTION;

			case TL:
			tl_label:

				/* Fetch heap adress */

				index = pop();

				/* Retrieve tail and see if it was a pointer */

				data = retrieve_tail(index);
				if (h->is_pointer[index + 1]) flag1 = 1;

				push(data);
				if (flag1) s.is_root[s.top] = 1;
				
				/* Reset flag */

				flag1 = 0;
				pc += 1;
				NEXT_INSTRUCTION;
        }

    }

bogus_label:

out:	
    return 0;

}
