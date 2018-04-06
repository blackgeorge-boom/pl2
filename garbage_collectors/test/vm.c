#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <time.h>

#define NEXTINSTRUCTION goto *(void *)(labeltab[*pc])

#define PROGRAMSIZE 65536

/*
 * In this machine, 32-bit signed int is the same as int.
 * Program can have up to 2^16 bytes of instructions.
 * Even if all instructions push to the stack (for example with push4), 
 * there will be pushed 2^16 / 2^5 = 2048 int numbers.
 * Thus, we define the appropriate stack size.
 */

#define STACKSIZE 2048 

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
    int data[STACKSIZE];
    int top;
};

typedef struct stack stack;

stack s;	/* Global stack */

/* Useful stack functions */

void stackinit() {
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

int getbytesigned (signed char *buff) {
	int result;
	result = buff[0];
	return result;
}

int get2bytessigned (signed char *buff) {
	int result;
	result = buff[0] | buff[1] << 8;
	return result;
}

int get4bytessigned (signed char *buff) {
	int result;
	result = buff[0] | buff[1] << 8 | buff[2] << 16 | buff[3] << 24;
	return result;
}

int getbyteunsigned (unsigned char *buff) {
	int result;
	result = buff[0];
	return result;
}

int get2bytesunsigned (unsigned char *buff) {
	int result;
	result = buff[0] | buff[1] << 8;
	return result;
}

int readprogram (char *filename, char *buffer) {

	FILE *fileptr;
	long filelen = 0;
	char c;

	fileptr = fopen(filename, "r");

	/* 
	 * Scan one byte at a time, till
	 * you reach the end of file.
	 */

	while (fscanf(fileptr, "%c", &c) != EOF) {
		buffer[filelen++] = c;
		//printf("%x ", c);
	} 

	//printf("\n");
			
	fclose(fileptr);

    return filelen;


}

int main(int argc, char const *argv[])
{
    char byteprogram[PROGRAMSIZE], *pc;
    short int opcode;
    int i, proglen, data, data1, data2;
	unsigned int jumpaddr, index;

	double timespent;
	clockt begin, end;

	/*
	 * Interpreter will be indirectly threaded, so we need
	 * a table of labels to guide us to the next instruction.
	 * Each instruction is mapped to a cell in the table, using 
	 * the op code as index.
	 * Bogus labels are used to preserve mapping for the clock
	 * bytecode instruction.
	 */

	static void *labeltab[] = {

		&&haltlabel,
		&&jumplabel,
		&&jnzlabel,
		&&duplabel,
		&&droplabel,
		&&push4label,
		&&push2label,
		&&push1label,
		&&addlabel,
		&&sublabel,
		&&mullabel,
		&&divlabel,
		&&modlabel,
		&&eqlabel,
		&&nelabel,
		&&ltlabel,
		&&gtlabel,
		&&lelabel,
		&&gelabel,
		&&notlabel,
		&&andlabel,
		&&orlabel,
		&&inlabel,
		&&outlabel,
		&&boguslabel,
		&&boguslabel,
		&&boguslabel,
		&&boguslabel,
		&&boguslabel,
		&&boguslabel,
		&&boguslabel,
		&&boguslabel,
		&&boguslabel,
		&&boguslabel,
		&&boguslabel,
		&&boguslabel,
		&&boguslabel,
		&&boguslabel,
		&&boguslabel,
		&&boguslabel,
		&&boguslabel,	
		&&boguslabel,
		&&clocklabel

	};

    
    //printf("Reading program bytecode...\n");

    proglen = readprogram(argv[1], byteprogram);

    //printf("Read %d bytes!\n", proglen);

    pc = &byteprogram[0];

//    for (i = 0; i < proglen; i++) //printf("%d ", byteprogram[i]);
	
	//printf("\n");

	//printf("Byte signed : %d\n", getbytesigned(&pc[77]));
	signed char c1 = pc[77];
	//printf("c1 is %d\n", c1);

	//printf("2 Bytes signed : %d\n", get2bytessigned(&pc[76]));

	//printf("4 Bytes signed : %d\n", get4bytessigned(pc));
	
	//printf("Byte unsigned : %d\n", getbyteunsigned(&pc[77]));
	unsigned char c2 = pc[77];
	//printf("c2 is %d\n", c2);

	//printf("2 Bytes unsigned : %d\n", get2bytesunsigned(&pc[76]));


	stackinit();
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

        nextinstruction:
		begin = clock();
        opcode = pc[0];
        switch (opcode) {

			case HALT:
			haltlabel:
				//printf("halt\n");
				goto out;

			case JUMP:
			jumplabel:
				//printf("jump\n");
				jumpaddr = get2bytesunsigned(&pc[1]);
				pc = &byteprogram[jumpaddr];
				NEXTINSTRUCTION;

			case JNZ:
			jnzlabel:
				//printf("jnz\n");
				data = pop();
				if (data != 0) {
					jumpaddr = get2bytesunsigned(&pc[1]);
					pc = &byteprogram[jumpaddr];
				}
				else pc += 3;
				NEXTINSTRUCTION;

			case DUP:
			duplabel:
				//printf("dup\n");
				index = getbyteunsigned(&pc[1]);
				data = find(index);
				push(data);
				pc += 2;	
				NEXTINSTRUCTION;

			case DROP:
			droplabel:
				//printf("drop\n");
				data = pop();
				pc += 1;
				NEXTINSTRUCTION;

			case PUSH4:
			push4label:
				//printf("push4\n");
				data = get4bytessigned(&pc[1]);
				push(data);
				pc += 5;
				NEXTINSTRUCTION;	
				
			case PUSH2:
			push2label:
				//printf("push2\n");
				data = get2bytessigned(&pc[1]);
				push(data);
				pc += 3;
				NEXTINSTRUCTION;	
				
			case PUSH1:
			push1label:
				//printf("push1\n");
				data = getbytesigned(&pc[1]);
				push(data);
				pc += 2;
				NEXTINSTRUCTION;	

			case ADD:
			addlabel:
				//printf("add\n");
				data1 = pop();
				data2 = pop();
				push(data1 + data2);
				pc += 1;
				NEXTINSTRUCTION;

			case SUB:
			sublabel:
				//printf("sub\n");
				data1 = pop();
				data2 = pop();
				push(data2 - data1);
				pc += 1;
				NEXTINSTRUCTION;
	
			case MUL:
			mullabel:
				//printf("mul\n");
				data1 = pop();
				data2 = pop();
				push(data1 * data2);
				pc += 1;
				NEXTINSTRUCTION;

			case DIV:
			divlabel:
				//printf("div\n");
				data1 = pop();
				data2 = pop();
				push(data2 / data1);
				pc += 1;
				NEXTINSTRUCTION;

			case MOD:
			modlabel:
				//printf("mod\n");
				data1 = pop();
				data2 = pop();
				push(data2 % data1);
				pc += 1;
				NEXTINSTRUCTION;

			case EQ:
			eqlabel:
				//printf("eq\n");
				data1 = pop();
				data2 = pop();
				push(data1 == data2);
				pc += 1;
				NEXTINSTRUCTION;

			case NE:
			nelabel:
				//printf("ne\n");
				data1 = pop();
				data2 = pop();
				push(data1 != data2);
				pc += 1;
				NEXTINSTRUCTION;

			case LT:
			ltlabel:
				//printf("lt\n");
				data1 = pop();
				data2 = pop();
				push(data2 < data1);
				pc += 1;
				NEXTINSTRUCTION;
			
			case GT:
			gtlabel:
				//printf("gt\n");
				data1 = pop();
				data2 = pop();
				push(data2 > data1);
				pc += 1;
				NEXTINSTRUCTION;
			
			case LE:
			lelabel:
				//printf("le\n");
				data1 = pop();
				data2 = pop();
				push(data2 <= data1);
				pc += 1;
				NEXTINSTRUCTION;
			
			case GE:
			gelabel:
				//printf("ge\n");
				data1 = pop();
				data2 = pop();
				push(data2 >= data1);
				pc += 1;
				NEXTINSTRUCTION;
			
			case NOT:
			notlabel:
				//printf("not\n");
				data = pop();
				push(data == 0);
				pc += 1;
				NEXTINSTRUCTION; 

			case AND: 
			andlabel:
				//printf("and\n");
				data1 = pop();
				data2 = pop();
				push(data1 != 0 && data2 != 0);
				pc += 1;
				NEXTINSTRUCTION;
				
			case OR: 
			orlabel:
				//printf("or\n");
				data1 = pop();
				data2 = pop();
				push(data1 != 0 || data2 != 0);
				pc += 1;
				NEXTINSTRUCTION;

			case IN:
			inlabel:
				//printf("in\n");
				scanf("%c", data);
				push(data);
				pc += 1;
				NEXTINSTRUCTION;

			case OUT:
			outlabel:
				//printf("out\n");
				data = pop();
				printf("%c", data);
				pc += 1;
				NEXTINSTRUCTION;
		   
			case CLOCK:
			clocklabel:
				//printf("clock\n");
				end = clock();
				timespent = (double)(end - begin) / CLOCKSPERSEC;
				printf("%0.6lf\n", timespent);	
				pc += 1;
				NEXTINSTRUCTION;

        }

    }

boguslabel:

out:	
    return 0;

}
