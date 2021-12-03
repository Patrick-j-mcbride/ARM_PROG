	/* We really can't beat the compiler much by just speeding up
	the negate function, but it gives the student an example. This
	assembly code gives about 2% speedup on the regression tests,
	so it is quite a bit faster than the C version. But it just is
	not used often enough to give more overall speedup. */
	
	.text
    .align 8
        .type   bigint_negate, %function
        .global bigint_negate
bigint_negate:
        stp     x29, x30, [sp, #-32]! // Save FP & Link Register x30
        stp     x19, x20, [sp, #16]   // Save non-volatile regs
        mov     x19, x0               // x19 = bigint b
        ldr     w20, [x19, #8]        // w20 = b->size
        // initialize bigint struct to hold result
        mov     w0, 0x10000000        // w0 = -MAX_INT
        cmp     w20, w0
        cinc    w20, w20, EQ          // increment size if -MAX_INT
        mov     w0, w20
        bl      bigint_alloc          // x0 = bigint_alloc(b->size)
        str     w20, [x0, #8]         // new->size = b->size
        ldr     x3, [x19]             // x3 = b->blks (src chunks)
        ldr     x4, [x0]              // x4 = new->blks(dest chunks)
        // loop from least significant chunk to most significant
        cmp     w20, wzr              // for(w20=size; w20>0; w20--)
        ble     endloop
        negs    xzr, xzr              // set carry flag to 1
loop:
        ldr     x6, [x3], #8          // load chunk from source
	ngcs	x6, x6                // negate it with carry, set flags
        str     x6, [x4], #8          // store chunk in destination
        sub     w20, w20, #1
        cbnz    w20, loop
endloop:
        // return address of new bigint is already in x0
        ldp     x19, x20, [sp, #16]     // Restore non-volatile regs
        ldp     x29, x30, [sp], #32     // Restore FP & LR
        ret
        .size   bigint_negate,(. - bigint_negate)
