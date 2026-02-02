; The Window Looks Back - 6502 Assembly
; For Commodore 64, Apple II, Atari 800
; SGR A* Cafe Window View

        .org $0801          ; C64 BASIC start

; BASIC stub: 10 SYS 2064
        .byte $0b,$08,$0a,$00,$9e,$32,$30,$36,$34,$00,$00,$00

start:
        ; Clear screen
        lda #$93
        jsr $ffd2

        ; Print title
        ldx #0
title_loop:
        lda title,x
        beq print_calc
        jsr $ffd2
        inx
        jmp title_loop

print_calc:
        ; Print observer distance
        ldx #0
obs_loop:
        lda observer_msg,x
        beq print_focal
        jsr $ffd2
        inx
        jmp obs_loop

print_focal:
        ; Print focal length
        ldx #0
focal_loop:
        lda focal_msg,x
        beq print_window
        jsr $ffd2
        inx
        jmp focal_loop

print_window:
        ; Print window distance
        ldx #0
window_loop:
        lda window_msg,x
        beq print_result
        jsr $ffd2
        inx
        jmp window_loop

print_result:
        ; Print result
        ldx #0
result_loop:
        lda result_msg,x
        beq done
        jsr $ffd2
        inx
        jmp result_loop

done:
        rts

; Data
title:
        .byte $0d,"WINDOW AT SGR A*",$0d,$0d,0

observer_msg:
        .byte "OBSERVER: 71",$0d,0

focal_msg:
        .byte "FOCAL: 196883",$0d,0

window_msg:
        .byte "WINDOW: -71.03",$0d,$0d,0

result_msg:
        .byte "VIRTUAL IMAGE",$0d
        .byte "INSIDE BLACK HOLE",$0d,$0d
        .byte "YOU ARE +1",$0d
        .byte "OBSERVER=OBSERVED",$0d,$0d
        .byte "WINDOW LOOKS BACK",$0d,0
