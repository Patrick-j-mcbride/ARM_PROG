 	    .text
         .align 8
        .type   bigint_adc, %function
        .global bigint_adc
bigint_adc:
        stp     x29, x30, [sp, #-16]!   // Save FP & Link Register x30
        stp     x24, x25, [sp, #-16]! 
        stp     x22, x23, [sp, #-16]!   
        stp     x20, x21, [sp, #-16]!
        mov     x22, x0                 // move L
        mov     x23, x1                 // move R            
        mov     x20, xzr
        
        ldr     w20, [x0, #8]           // size L
        mov     x21, xzr
        ldr     w21, [x1, #8]           // size R
        mov     x25, x2                 // move carry

        cmp     w20, w21                // compair size of L and R

        bgt     bigL
        blt     bigR

eqRL:    // L and R are equal size
        add     x0, x20, #1             // put size+1 into x0
        bl      bigint_alloc            // allocate new bigint             
        ldr     x22, [x22]
        mov     x5, xzr
        ldr     x23, [x23]
        ldr     x24, [x0]

eqLRAddLoop:   // L and R are equal size loop
        cmp     w21, #1         // compair itr to 1
        ble     eqTopChunkAdd            // check if done
        sub     w21, w21, #1    // itr--

        ldr     x12, [x22], #8               // L chunk 
        adds    x10, x25, x12                // L+C      
        ldr     x13, [x23], #8               // R chunk 
        mov     x25, xzr
        adcs    x25, x5, xzr               
        adds    x10, x10, x13
        adc     x25, x5, xzr
        str     x10, [x24], #8
        b       eqLRAddLoop
eqTopChunkAdd:
        ldr     x12, [x22], #8               // L chunk      
        ldr     x13, [x23], #8               // R chunk 
        lsr     x2, x12, #63
        lsr     x3, x13, #63
        cmp     x2, x3 
        beq     eqSameSign
eqMixSigns:
        adds    x10, x25, x12                // L+C       
        mov     x25, xzr
        adcs    x25, x5, xzr               
        adds    x10, x10, x13
        adc     x25, x5, xzr
        str     x10, [x24], #8
        asr     x10, x10, #63
        str     x10, [x24]
        b       trimAndReturn
eqSameSign:
        cmp     x2, #1
        beq     eqBothNegative 
eqBothPositive:
        adds    x10, x25, x12                // L+C       
        mov     x25, xzr
        adcs    x25, x5, xzr               
        adds    x10, x10, x13
        adc     x25, x5, xzr
        str     x10, [x24], #8
        str     x25, [x24]
        b       trimAndReturn
eqBothNegative:
        adds    x10, x25, x12                // L+C       
        mov     x25, xzr
        adcs    x25, x5, xzr               
        adds    x10, x10, x13
        adc     x25, x5, xzr
        str     x10, [x24], #8
        mov     x25, 0xFFFFFFFFFFFFFFFF
        str     x25, [x24]
        b       trimAndReturn



bigL:   // L is biger
        add     x0, x20, #1             // put L.size+1 into x0
        bl      bigint_alloc            // allocate new bigint             
        ldr     x22, [x22]
        sub     x20, x20, x21
        ldr     x23, [x23]
        ldr     x24, [x0]
        mov     x5, xzr

bigLTopAddLoop:   // L > R loop
        cmp     w21, #1         // compair itr to 1
        ble     bigLFirstStop            // check if done
        sub     w21, w21, #1    // itr--

        ldr     x12, [x22], #8               // L chunk 
        adds    x10, x25, x12                // L+C      
        ldr     x13, [x23], #8               // R chunk 
        mov     x25, xzr
        adcs    x25, x5, xzr               
        adds    x10, x10, x13
        adc     x25, x5, xzr
        str     x10, [x24], #8
        b       bigLTopAddLoop
bigLFirstStop:
        ldr     x12, [x22], #8               // L chunk 
        adds    x10, x25, x12                // L+C      
        ldr     x13, [x23]               // R chunk 
        mov     x25, xzr
        adcs    x25, x5, xzr               
        adds    x10, x10, x13
        adc     x25, x5, xzr
        str     x10, [x24], #8
        asr     x13, x13, #63

bigLBottomAddLoop:
        cmp     w20, #1         // compair itr to 1
        ble     bigLFinalStop            // check if done
        sub     w20, w20, #1    // itr--

        ldr     x12, [x22], #8               // L chunk 
        adds    x10, x25, x12                // L+C      
        mov     x25, xzr
        adcs    x25, x5, xzr               
        adds    x10, x10, x13
        adc     x25, x5, xzr
        str     x10, [x24], #8
        b       bigLBottomAddLoop
bigLFinalStop:
        ldr     x12, [x22], #8               // L chunk      
        lsr     x2, x12, #63
        mov     x3, x13
        cmp     x2, x3 
        beq     bigLSameSigns
bigLMixedSigns:
        adds    x10, x25, x12                // L+C       
        mov     x25, xzr
        adcs    x25, x5, xzr               
        adds    x10, x10, x13
        adc     x25, x5, xzr
        str     x10, [x24], #8
        asr     x10, x10, #63
        str     x10, [x24]
        b       trimAndReturn
bigLSameSigns:
        cmp     x2, #1
        beq     bigLBothNegative 
bigLBothPositive:
        adds    x10, x25, x12                // L+C       
        mov     x25, xzr
        adcs    x25, x5, xzr               
        adds    x10, x10, x13
        adc     x25, x5, xzr
        str     x10, [x24], #8
        str     x25, [x24]
        b       trimAndReturn
bigLBothNegative:
        adds    x10, x25, x12                // L+C       
        mov     x25, xzr
        adcs    x25, x5, xzr               
        adds    x10, x10, x13
        adc     x25, x5, xzr
        str     x10, [x24], #8
        mov     x25, 0xFFFFFFFFFFFFFFFF
        str     x25, [x24]
        b       trimAndReturn

bigR:   // R is biger
        add     x0, x21, #1             // put L.size+1 into x0
        bl      bigint_alloc            // allocate new bigint             
        ldr     x22, [x22]
        sub     x21, x21, x20
        ldr     x23, [x23]
        ldr     x24, [x0]
        mov     x5, xzr

bigRTopAddLoop:   // L > R loop
        cmp     w20, #1         // compair itr to 1
        ble     bigRFirstStop            // check if done
        sub     w20, w20, #1    // itr--

        ldr     x12, [x22], #8               // L chunk 
        adds    x10, x25, x12                // L+C      
        ldr     x13, [x23], #8               // R chunk 
        mov     x25, xzr
        adcs    x25, x5, xzr               
        adds    x10, x10, x13
        adc     x25, x5, xzr
        str     x10, [x24], #8
        b       bigRTopAddLoop
bigRFirstStop:
        ldr     x13, [x23], #8               // L chunk 
        adds    x10, x25, x13                // R+C      
        ldr     x12, [x22]               // L chunk 
        mov     x25, xzr
        adcs    x25, x5, xzr               
        adds    x10, x10, x12
        adc     x25, x5, xzr
        str     x10, [x24], #8
        asr     x12, x12, #63

bigRBottomAddLoop:
        cmp     w21, #1         // compair itr to 1
        ble     bigRFinalStop            // check if done
        sub     w21, w21, #1    // itr--

        ldr     x13, [x23], #8               // L chunk 
        adds    x10, x25, x13                // L+C      
        mov     x25, xzr
        adcs    x25, x5, xzr               
        adds    x10, x10, x12
        adc     x25, x5, xzr
        str     x10, [x24], #8
        b       bigRBottomAddLoop
bigRFinalStop:
        ldr     x13, [x23], #8               // L chunk      
        lsr     x3, x13, #63
        mov     x2, x12
        cmp     x2, x3 
        beq     bigRSameSigns
bigRMixedSigns:
        adds    x10, x25, x12                // L+C       
        mov     x25, xzr
        adcs    x25, x5, xzr               
        adds    x10, x10, x13
        adc     x25, x5, xzr
        str     x10, [x24], #8
        asr     x10, x10, #63
        str     x10, [x24]
        b       trimAndReturn
bigRSameSigns:
        cmp     x2, #1
        beq     bigRBothNegative 
bigRBothPositive:
        adds    x10, x25, x12                // L+C       
        mov     x25, xzr
        adcs    x25, x5, xzr               
        adds    x10, x10, x13
        adc     x25, x5, xzr
        str     x10, [x24], #8
        str     x25, [x24]
        b       trimAndReturn
bigRBothNegative:
        adds    x10, x25, x12                // L+C       
        mov     x25, xzr
        adcs    x25, x5, xzr               
        adds    x10, x10, x13
        adc     x25, x5, xzr
        str     x10, [x24], #8
        mov     x25, 0xFFFFFFFFFFFFFFFF
        str     x25, [x24]
        b       trimAndReturn

trimAndReturn:
        bl      bigint_fast_trim
        ldp     x20, x21, [sp], #16   
        ldp     x22, x23, [sp], #16  
        ldp     x24, x25, [sp], #16    
        ldp     x29, x30, [sp], #16     // Restore FP & LR
        ret
.size   bigint_adc,(. - bigint_adc)
 