    .text
    .align 8
        .type   bigint_cmp, %function
        .global bigint_cmp
bigint_cmp:
        stp     x29, x30, [sp, #-16]!   // Save FP & Link Register x30
        mov     x10, xzr
        ldr     w10, [x0, #8]           // size L
        mov     x11, xzr
        ldr     w11, [x1, #8]           // size R

        cmp     w10, w11                // compair size of L and R
        bgt     bigL
        blt     bigR
eRL:    // L and R are equal size
        ldr     x12, [x0]               // adr to first L chunk
        sub     x4, x10, #1             // size-1        
        ldr     x13, [x1]               // adr to first R chunk        
        lsl     x4, x4, #3              // multiply by 8 to get adr of largest chunk

        ldr     x2, [x12, x4]
        lsr     x2, x2, #63
        ldr     x3, [x13, x4]
        lsr     x3, x3, #63
        cmp     x2, x3  
        beq     prElp

        cmp     x2, xzr 
        beq     retG
        bgt     retL  
prElp:            
        add     x14, x12, x4
        add     x15, x13, x4

elop:   // L and R are equal size loop
        cmp     w10, wzr
        ble     retE
        ldr     x2, [x14]
        sub     w10, w10, #1 
        sub     x14, x14, #8
        ldr     x3, [x15]
        sub     x15, x15, #8
        cmp     x2, x3                  // compair most signifigant chunk of L to R
        beq     elop
        blo     retL
        mov     x0, #1
        ldp     x29, x30, [sp], #16     // Restore FP & LR
        ret

bigL:   // L is biger
        ldr     x12, [x0]               // adr to first L chunk
        sub     x4, x10, #1             // size-1  
        ldr     x2, [x12, x4, lsl #3]
        lsr     x2, x2, #63
        cmp     x2, xzr                 // compair most signifigant chunk of L to 0
        bgt     retL
        mov     x0, #1
        ldp     x29, x30, [sp], #16     // Restore FP & LR
        ret

bigR:   // R is biger
        ldr     x13, [x1]               // adr to first R chunk
        sub     x5, x11, #1             // size-1  
        ldr     x3, [x13, x5, lsl #3] 
        lsr     x3, x3, #63
        cmp     x3, xzr
        beq     retL
        mov     x0, #1
        ldp     x29, x30, [sp], #16     // Restore FP & LR
        ret


retG:
        mov     x0, #1
        ldp     x29, x30, [sp], #16     // Restore FP & LR
        ret
retE:
        mov     x0, xzr
        ldp     x29, x30, [sp], #16     // Restore FP & LR
        ret
retL:
        mov     x0, #-1
        ldp     x29, x30, [sp], #16     // Restore FP & LR
        ret
cmpD:
        ldp     x29, x30, [sp], #16     // Restore FP & LR
        ret
        .size   bigint_cmp,(. - bigint_cmp)
