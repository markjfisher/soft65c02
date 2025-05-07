        .export     _fn_under_test
        .export     x_loop

        .include    "zeropage.inc"

; this is some function under test, could be any name any code
_fn_under_test:
    ldx     #$10

x_loop:
    stx     tmp1
    dex
    bne     x_loop
    
    rts
