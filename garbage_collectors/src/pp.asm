0000    push1   0x0011
0x0002  dup     0000
0x0004  jnz     0x000b
0x0007  drop
0x0008  jump    0x0089
0x000b  push1   0x0001
0x000d  sub
0x000e  push1   0x002a
0x0010  dup     0000
0x0012  jnz     0x0019
0x0015  drop
0x0016  jump    0x0080
0x0019  push1   0x0001
0x001b  sub
0x001c  push2   0x03e8
0x001f  dup     0000
0x0021  jnz     0x0028
0x0024  drop
0x0025  jump    0x007a
0x0028  push1   0x0001
0x002a  sub
0x002b  push1   0000
0x002d  push1   0x0001
0x002f  dup     0000
0x0031  push2   0x03e8
0x0034  gt
0x0035  jnz     0x0046
0x0038  dup     0x0001
0x003a  cons
0x003b  cons
0x003c  tl
0x003d  dup     0000
0x003f  hd
0x0040  push1   0x0001
0x0042  add
0x0043  jump    0x002f
0x0046  drop
0x0047  push2   0x03e8
0x004a  dup     0x0001
0x004c  cons
0x004d  cons
0x004e  tl
0x004f  dup     0000
0x0051  hd
0x0052  dup     0000
0x0054  jnz     0x005a
0x0057  jump    0x0072
0x005a  dup     0x0001
0x005c  tl
0x005d  hd
0x005e  ne
0x005f  jnz     0x008b 
0x0062  tl
0x0063  dup     0000
0x0065  hd
0x0066  push1   0x0001
0x0068  sub
0x0069  dup     0x0001
0x006b  tl
0x006c  cons
0x006d  cons
0x006e  tl
0x006f  jump    0x004f
0x0072  drop
0x0073  tl
0x0074  jnz     0x008b
0x0077  jump    0x001f
0x007a  push1   0x002e
0x007c  output
0x007d  jump    0x0010
0x0080  push1   0x0024
0x0082  output
0x0083  push1   0x000a
0x0085  output
0x0086  jump    0x0002
0x0089  clock
0x008a  halt
0x008b  push1   0000
0x008d  push1   0x000a
0x008f  push1   0x0021
0x0091  push1   0x0073
0x0093  push1   0x006c
0x0095  push1   0x006c
0x0097  push1   0x0065
0x0099  push1   0x0063
0x009b  push1   0x0020
0x009d  push1   0x0073
0x009f  push1   0x006e
0x00a1  push1   0x006f
0x00a3  push1   0x0063
0x00a5  push1   0x0020
0x00a7  push1   0x0068
0x00a9  push1   0x0074
0x00ab  push1   0x0069
0x00ad  push1   0x0077
0x00af  push1   0x0020
0x00b1  push1   0x0067
0x00b3  push1   0x006e
0x00b5  push1   0x006f
0x00b7  push1   0x0072
0x00b9  push1   0x0077
0x00bb  push1   0x0020
0x00bd  push1   0x0067
0x00bf  push1   0x006e
0x00c1  push1   0x0069
0x00c3  push1   0x0068
0x00c5  push1   0x0074
0x00c7  push1   0x0065
0x00c9  push1   0x006d
0x00cb  push1   0x006f
0x00cd  push1   0x0073
0x00cf  push1   0x0020
0x00d1  push1   0x003a
0x00d3  push1   0x0072
0x00d5  push1   0x006f
0x00d7  push1   0x0072
0x00d9  push1   0x0072
0x00db  push1   0x0045
0x00dd  dup     0000
0x00df  jnz     0x00e6
0x00e2  drop
0x00e3  jump    0x00ea
0x00e6  output
0x00e7  jump    0x00dd
0x00ea  halt
