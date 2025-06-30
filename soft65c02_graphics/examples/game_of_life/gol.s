        .export _main
        .export _debug
        .export _process_generation
        .export _reset_gol

; Conway's Game of Life for 65C02
; This version uses Rust "DMA" acceleration for computation but
; the 6502 handles input polling and game control logic

; Memory locations  
KEYBOARD_INPUT  = $8030     ; Keyboard input buffer (16 bytes at 0x8030-0x803F)
PAUSE_FLAG      = $8040     ; Pause toggle flag (0=running, 1=paused)
KEY_R           = $1C       ; R key code for reset
KEY_P           = $1A       ; P key code for pause

_main:
        ; Main game loop - let the 6502 do real work!
        jsr     _check_input    ; Check for keyboard input first
        jsr     _process_generation
        clc
        bcc     _main

_check_input:
        ; Read keyboard input location
        lda     KEYBOARD_INPUT
        beq     @no_input       ; Zero means no key pressed
        
        ; Check if it's the R key (reset)
        cmp     #KEY_R
        beq     @handle_reset
        
        ; Check if it's the P key (pause)
        cmp     #KEY_P
        beq     @handle_pause
        
        ; Other key - just clear and continue
        jmp     @clear_input
        
@handle_reset:
        ; R key pressed - reset the game!
        jsr     _reset_gol      ; Call reset routine (trapped by Rust)
        jmp     @clear_input
        
@handle_pause:
        ; P key pressed - toggle pause flag
        lda     PAUSE_FLAG
        eor     #$01            ; Toggle bit 0 (0->1, 1->0)
        sta     PAUSE_FLAG
        ; Fall through to clear input
        
@clear_input:
        ; Clear the input event so we don't process it again
        lda     #$00
        sta     KEYBOARD_INPUT
        
@no_input:
        rts

_process_generation:
        ; This will be trapped by Rust for fast computation
        rts

_reset_gol:
        ; This will be trapped by Rust to reset to random pattern
        rts

_debug:
        rts
