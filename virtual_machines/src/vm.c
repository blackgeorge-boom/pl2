#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <time.h>

#define NEXT_INSTRUCTION goto *(void *)(label_tab[*pc])

#define PROGRAM_SIZE 65536

/*
 * In this machine, 32-bit signed int is the same as int.
 * We give 4MB of stack memory. Stack will be an int array.
 * Thus, we define the appropriate stack size:
 * 4MB / 4B = 1048576 integers.
 */

#define STACK_SIZE 1048576 

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

/* Simple stack containing 32-bit signed integers */

struct stack {
    int data[STACK_SIZE];
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

int get_byte_signed (signed char *buff) {
	int result;
	result = buff[0];
	return result;
}

int get_2_bytes_signed (signed char *buff) {
	int result;
	result = buff[0] | buff[1] << 8;
	return result;
}

int get_4_bytes_signed (signed char *buff) {
	int result;
	result = buff[0] | buff[1] << 8 | buff[2] << 16 | buff[3] << 24;
	return result;
}

int get_byte_unsigned (unsigned char *buff) {
	int result;
	result = buff[0];
	return result;
}

int get_2_bytes_unsigned (unsigned char *buff) {
	int result;
	result = buff[0] | buff[1] << 8;
	return result;
}

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
	} 

	fclose(fileptr);

    return file_len;


}

int main(int argc, char const *argv[])
{
    char byte_program[PROGRAM_SIZE], *pc;
    short int opcode;
    int i, prog_len, data, data1, data2;
	unsigned int jump_addr, index;

	double time_spent;
	clock_t begin, end;

	/*
	 * Interpreter will be indirectly threaded, so we need
	 * a table of labels to guide us to the next instruction.
	 * Each instruction is mapped to a cell in the table, using 
	 * the op code as index.
	 * Bogus labels are used to preserve mapping for the clock
	 * bytecode instruction.
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
		&&clock_label

	};

    

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
				jump_addr = get_2_bytes_unsigned(&pc[1]);
				pc = &byte_program[jump_addr];
				NEXT_INSTRUCTION;

			case JNZ:
			jnz_label:
				data = pop();
				if (data != 0) {
					jump_addr = get_2_bytes_unsigned(&pc[1]);
					pc = &byte_program[jump_addr];
				}
				else pc += 3;
				NEXT_INSTRUCTION;

			case DUP:
			dup_label:
				index = get_byte_unsigned(&pc[1]);
				data = find(index);
				push(data);
				pc += 2;	
				NEXT_INSTRUCTION;

			case DROP:
			drop_label:
				data = pop();
				pc += 1;
				NEXT_INSTRUCTION;

			case PUSH4:
			push4_label:
				data = get_4_bytes_signed(&pc[1]);
				push(data);
				pc += 5;
				NEXT_INSTRUCTION;	
				
			case PUSH2:
			push2_label:
				data = get_2_bytes_signed(&pc[1]);
				push(data);
				pc += 3;
				NEXT_INSTRUCTION;	
				
			case PUSH1:
			push1_label:
				data = get_byte_signed(&pc[1]);
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

        }

    }

bogus_label:

out:	
    return 0;

}
