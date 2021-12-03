    .text
    .align 8
        .type   bigint_zero, %function
        .global bigint_zero
bigint_zero:
        stp     x29, x30, [sp, #-16]!   // Save FP & Link Register x30
        mov     x10, xzr
        ldr     w10, [x0, #8]           

        cmp     w10, #1                // compair size
        beq     sizeGood

        mov     x0, xzr
        stp     x29, x30, [sp], #16
        ret

sizeGood:
        ldr     x13, [x0]
        ldr     x4, [x13]
        cmp     x4, xzr

        bne     notZero

        mov     x0,#1
        stp     x29, x30, [sp], #16
        ret        
notZero:
        mov     x0, xzr
        stp     x29, x30, [sp], #16
        ret

        .size   bigint_zero,(. - bigint_zero)
