#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <time.h>

#define NEXT_INSTRUCTION goto *(void *)(label_tab[*pc])

#define PROGRAM_SIZE 65536

/*
 * In this machine, 32-bit signed int is the same as int.
 * Program can have up to 2^16 bytes of instructions.
 * Even if all instructions push to the stack (for example with push4), 
 * there will be pushed 2^16 / 2^5 = 2048 int numbers.
 * Thus, we define the appropriate stack size.
 */

#define STACK_SIZE 2048 

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
		//printf("%x ", c);
	} 

	//printf("\n");
			
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

    
    //printf("Reading program bytecode...\n");

    prog_len = read_program(argv[1], byte_program);

    //printf("Read %d bytes!\n", prog_len);

    pc = &byte_program[0];

//    for (i = 0; i < prog_len; i++) //printf("%d ", byte_program[i]);
	
	//printf("\n");

	//printf("Byte signed : %d\n", get_byte_signed(&pc[77]));
	signed char c1 = pc[77];
	//printf("c1 is %d\n", c1);

	//printf("2 Bytes signed : %d\n", get_2_bytes_signed(&pc[76]));

	//printf("4 Bytes signed : %d\n", get_4_bytes_signed(pc));
	
	//printf("Byte unsigned : %d\n", get_byte_unsigned(&pc[77]));
	unsigned char c2 = pc[77];
	//printf("c2 is %d\n", c2);

	//printf("2 Bytes unsigned : %d\n", get_2_bytes_unsigned(&pc[76]));


	stack_init();
	push(1);
	push(2);
	push(3);
	//printf("0 index : %d\n", find(0));
	//printf("1 index : %d\n", find(1));
	//printf("popping : %d\n", pop());
	//printf("1 index : %d\n", find(1));
	pop();
	pop();
	pop();
//	//printf("1 index : %d\n", find(1));


    while(1) {

        next_instruction:
		begin = clock();
        opcode = pc[0];
        switch (opcode) {

			case HALT:
			halt_label:
				//printf("halt\n");
				goto out;

			case JUMP:
			jump_label:
				//printf("jump\n");
				jump_addr = get_2_bytes_unsigned(&pc[1]);
				pc = &byte_program[jump_addr];
				NEXT_INSTRUCTION;

			case JNZ:
			jnz_label:
				//printf("jnz\n");
				data = pop();
				if (data != 0) {
					jump_addr = get_2_bytes_unsigned(&pc[1]);
					pc = &byte_program[jump_addr];
				}
				else pc += 3;
				NEXT_INSTRUCTION;

			case DUP:
			dup_label:
				//printf("dup\n");
				index = get_byte_unsigned(&pc[1]);
				data = find(index);
				push(data);
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
				//printf("push4\n");
				data = get_4_bytes_signed(&pc[1]);
				push(data);
				pc += 5;
				NEXT_INSTRUCTION;	
				
			case PUSH2:
			push2_label:
				//printf("push2\n");
				data = get_2_bytes_signed(&pc[1]);
				push(data);
				pc += 3;
				NEXT_INSTRUCTION;	
				
			case PUSH1:
			push1_label:
				//printf("push1\n");
				data = get_byte_signed(&pc[1]);
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

        }

    }

bogus_label:

out:	
    return 0;

}
