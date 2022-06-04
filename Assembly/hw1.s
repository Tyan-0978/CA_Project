.data
    n: .word 11
.text
.globl __start

FUNCTION:
    # Save return address and n on stack
    # addi sp, sp, -16  (change to sub)
    addi x18, x0, 16
    sub sp, sp, x18
    sw x1, 8(sp)
    sw x10, 0(sp)
    
    # three cases
    
    # x31=10, x30=1
    addi x31, x0, 10
    addi x30, x0, 1
    
    # if n>=10
    bge x10, x31, N_LARGETHAN_10
    # if 1<=n<10
    bge x10, x30, N_LARGETHAN_1
    # if n==0
    beq x10, x0, N_EQUAL_0
    
N_LARGETHAN_10:
  # For 2*T(3n/4)
    # after the 3 lines, n = (3/4) * n
    slli x31, x10, 1
    add x10, x10, x31
    srli x10, x10, 2
    # call T((3/4)n), after the line, x5 = T((3/4)n), then x5 = x5*2
    jal x1, FUNCTION
    slli x5, x5, 1
  # For 0.875 aka 7/8n
    # after the 3 lines, x30 = (7/8) * n
    lw x31, 0(sp)
    slli x30, x31, 3
    sub x30, x30, x31
    srli x30, x30, 3
    # + (7/8)n
    add x5, x5, x30
  # For -137
    # addi x5, x5, -137  (change to sub)
    addi x18, x0, 137
    sub x5, x5, x18
  # return
    lw   x1, 8(sp)
    addi sp, sp, 16
    jalr x0, 0(x1)

N_LARGETHAN_1:
    # n = n-1
    # addi x10, x10, -1  (change to sub)
    addi x18, x0, 1
    sub x10, x10, x18
    # call T(n-1), after the line, x5 = T(n-1)
    jal x1, FUNCTION
    # T(n) = 2 * T(n-1)
    slli x5, x5, 1
    # return
    lw   x1, 8(sp)
    addi sp, sp, 16
    jalr x0, 0(x1)

N_EQUAL_0:
    # base case, put 7 in x5 (output)
    addi x5, x0, 7
    # return
    lw   x1, 8(sp)
    addi sp, sp, 16
    jalr x0, 0(x1)
    
# Do NOT modify this part!!!
__start:
    la   t0, n
    lw   x10, 0(t0)
    jal  x1,FUNCTION
    la   a0, n
    sw   t0, 4(a0)
    addi a0,x0,10
    ecall
