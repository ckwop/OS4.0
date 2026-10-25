// text.s: terminal input, parsing, dictionary lookup, number conversion and
// text output, as subroutines for the outer interpreter and compiler.
// Included by kernel.s.

	.text
	.global	type_sub, print_hex_sub, print_udec_sub	// for platform code, e.g. exception reports

// refill_sub: make the next line of input current. Reads core.fs line by line,
// then the terminal. Exits through hal_bye when terminal input ends.
refill_sub:
	stp	x29, x30, [sp, #-16]!
	ldr	x0, =var_source
	ldr	x0, [x0]
	cbz	x0, 4f
	ldr	x0, =var_boot_pos
	ldr	x1, [x0]
	ldr	x2, =boot_src_end
	cmp	x1, x2
	b.hs	3f
	str	x1, [UP, #U_TIB]
	mov	x3, x1
1:	cmp	x3, x2
	b.hs	2f
	ldrb	w4, [x3]
	cmp	w4, #CH_LF
	b.eq	2f
	add	x3, x3, #1
	b	1b
2:	sub	x4, x3, x1
	str	x4, [UP, #U_NTIB]
	add	x3, x3, #1
	str	x3, [x0]
	ldr	x0, =var_boot_line
	ldr	x1, [x0]
	add	x1, x1, #1
	str	x1, [x0]
	b	5f
3:	ldr	x0, =var_source		// core.fs is done: read the terminal from now on
	str	xzr, [x0]
	ldr	x0, =msg_banner
	mov	x1, #msg_banner_len
	bl	type_sub
4:	ldr	x0, =tib_buf
	str	x0, [UP, #U_TIB]
	mov	x1, #TIB_SIZE
	bl	accept_sub
	str	x0, [UP, #U_NTIB]
5:	str	xzr, [UP, #U_TOIN]
	ldp	x29, x30, [sp], #16
	ret

// accept_sub: x0 buffer, x1 capacity -> x0 length. Reads a line from the terminal,
// echoing it, since a serial console does not echo for us. Backspace rubs out;
// Enter echoes a space. At end of input, finishes the line, then exits on the next call.
accept_sub:
	stp	x29, x30, [sp, #-48]!
	stp	x24, x25, [sp, #16]
	str	x26, [sp, #32]
	mov	x24, x0
	mov	x25, x1
	mov	x26, #0
	ldr	x0, =var_eof
	ldr	x0, [x0]
	cbnz	x0, 9f
1:	bl	hal_key
	cmn	x0, #1
	b.eq	7f
	cmp	x0, #CH_LF
	b.eq	8f
	cmp	x0, #CH_CR
	b.eq	8f
	cmp	x0, #CH_EOT
	b.eq	6f
	cmp	x0, #CH_BS
	b.eq	5f
	cmp	x0, #CH_DEL
	b.eq	5f
	cmp	x0, #CH_TAB
	b.ne	2f
	mov	x0, #CH_SPACE
2:	cmp	x0, #CH_SPACE
	b.lo	1b			// ignore other control characters
	cmp	x26, x25
	b.hs	1b			// line full
	strb	w0, [x24, x26]
	add	x26, x26, #1
	bl	hal_emit
	b	1b
5:	cbz	x26, 1b			// backspace
	sub	x26, x26, #1
	mov	x0, #CH_BS
	bl	hal_emit
	mov	x0, #CH_SPACE
	bl	hal_emit
	mov	x0, #CH_BS
	bl	hal_emit
	b	1b
6:	cbnz	x26, 1b			// Ctrl-D ends input only on an empty line
7:	cbz	x26, 9f			// end of input
	ldr	x0, =var_eof
	mov	x1, #1
	str	x1, [x0]
8:	mov	x0, #CH_SPACE
	bl	hal_emit
	mov	x0, x26
	ldr	x26, [sp, #32]
	ldp	x24, x25, [sp, #16]
	ldp	x29, x30, [sp], #48
	ret
9:	mov	x0, #0
	b	hal_bye

// parse_name_sub: -> x0 address, x1 length of the next space-delimited word
// in the current line (length 0 at the end of the line). Advances >in.
parse_name_sub:
	ldr	x2, [UP, #U_TIB]
	ldr	x3, [UP, #U_NTIB]
	ldr	x4, [UP, #U_TOIN]
1:	cmp	x4, x3			// skip leading spaces and control characters
	b.hs	4f
	ldrb	w5, [x2, x4]
	cmp	w5, #CH_SPACE
	b.hi	2f
	add	x4, x4, #1
	b	1b
2:	add	x0, x2, x4
	mov	x6, x4
3:	add	x4, x4, #1
	cmp	x4, x3
	b.hs	5f
	ldrb	w5, [x2, x4]
	cmp	w5, #CH_SPACE
	b.hi	3b
	sub	x1, x4, x6
	add	x4, x4, #1		// consume the delimiter
	str	x4, [UP, #U_TOIN]
	ret
4:	add	x0, x2, x4
	mov	x1, #0
	str	x4, [UP, #U_TOIN]
	ret
5:	sub	x1, x4, x6
	str	x4, [UP, #U_TOIN]
	ret

// parse_sub: x0 delimiter -> x0 address, x1 length of the text up to the
// delimiter or the end of the line. Advances >in past the delimiter.
parse_sub:
	ldr	x2, [UP, #U_TIB]
	ldr	x3, [UP, #U_NTIB]
	ldr	x4, [UP, #U_TOIN]
	add	x5, x2, x4
	mov	x6, x4
1:	cmp	x4, x3
	b.hs	2f
	ldrb	w7, [x2, x4]
	cmp	w7, w0
	b.eq	3f
	add	x4, x4, #1
	b	1b
2:	sub	x1, x4, x6
	str	x4, [UP, #U_TOIN]
	mov	x0, x5
	ret
3:	sub	x1, x4, x6
	add	x4, x4, #1
	str	x4, [UP, #U_TOIN]
	mov	x0, x5
	ret

// find_sub: x0 name, x1 length -> x0 xt (0 if not found), x1 1 if immediate,
// else -1. Case-insensitive; skips hidden words.
find_sub:
	ldr	x2, =var_latest
	ldr	x2, [x2]
1:	cbz	x2, 9f
	ldrb	w3, [x2, #8]
	tst	w3, #F_HIDDEN
	b.ne	8f
	and	w4, w3, #F_LENMASK
	cmp	x4, x1
	b.ne	8f
	add	x5, x2, #9
	mov	x6, #0
2:	cmp	x6, x1
	b.hs	3f
	ldrb	w7, [x0, x6]
	ldrb	w9, [x5, x6]
	TOLOWER	w7, w10
	TOLOWER	w9, w10
	cmp	w7, w9
	b.ne	8f
	add	x6, x6, #1
	b	2b
3:	add	x0, x5, x1		// the xt follows the name, 8-byte aligned
	add	x0, x0, #7
	and	x0, x0, #-8
	mov	x1, #-1
	mov	x6, #1
	tst	w3, #F_IMMED
	csel	x1, x6, x1, ne
	ret
8:	ldr	x2, [x2]
	b	1b
9:	mov	x0, #0
	mov	x1, #0
	ret

// number_sub: x0 text, x1 length -> x0 value, x1 1 if it is a number, else 0.
// Accepts an optional '-', then an optional base prefix ($ hex, # decimal,
// % binary), then digits in that base; or a character literal such as 'A'.
number_sub:
	mov	x2, x0
	add	x3, x0, x1
	ldr	x4, [UP, #U_BASE]
	mov	x5, #0			// negative?
	mov	x6, #0			// value
	cmp	x1, #3
	b.ne	1f
	ldrb	w7, [x2]
	cmp	w7, #CH_QUOTE
	b.ne	1f
	ldrb	w7, [x2, #2]
	cmp	w7, #CH_QUOTE
	b.ne	1f
	ldrb	w0, [x2, #1]
	mov	x1, #1
	ret
1:	cmp	x2, x3
	b.hs	9f
	ldrb	w7, [x2]
	cmp	w7, #CH_MINUS
	b.ne	2f
	mov	x5, #1
	add	x2, x2, #1
	cmp	x2, x3
	b.hs	9f
	ldrb	w7, [x2]
2:	mov	x8, #16
	cmp	w7, #CH_DOLLAR
	b.eq	3f
	mov	x8, #10
	cmp	w7, #CH_HASH
	b.eq	3f
	mov	x8, #2
	cmp	w7, #CH_PERCENT
	b.ne	4f
3:	mov	x4, x8
	add	x2, x2, #1
4:	cmp	x2, x3			// at least one digit
	b.hs	9f
5:	ldrb	w7, [x2]
	TOLOWER	w7, w9
	sub	w8, w7, #CH_0
	cmp	w8, #9
	b.ls	6f
	sub	w8, w7, #CH_A_LOWER
	cmp	w8, #25
	b.hi	9f
	add	w8, w8, #10
6:	cmp	x8, x4
	b.hs	9f
	madd	x6, x6, x4, x8
	add	x2, x2, #1
	cmp	x2, x3
	b.lo	5b
	cbz	x5, 7f
	neg	x6, x6
7:	mov	x0, x6
	mov	x1, #1
	ret
9:	mov	x0, #0
	mov	x1, #0
	ret

// type_sub: x0 address, x1 length -> emit each character.
type_sub:
	stp	x29, x30, [sp, #-32]!
	stp	x24, x25, [sp, #16]
	mov	x24, x0
	add	x25, x0, x1
1:	cmp	x24, x25
	b.hs	2f
	ldrb	w0, [x24], #1
	bl	hal_emit
	b	1b
2:	ldp	x24, x25, [sp, #16]
	ldp	x29, x30, [sp], #32
	ret

// print_hex_sub: x0 number -> print it as 16 hex digits.
print_hex_sub:
	stp	x29, x30, [sp, #-32]!	// digits are built in sp+16 .. sp+32
	add	x2, sp, #16
	mov	x3, #60
1:	lsr	x4, x0, x3
	and	x4, x4, #0xf
	cmp	x4, #10
	add	x5, x4, #CH_0
	add	x6, x4, #(CH_A_LOWER - 10)
	csel	x5, x6, x5, hs
	strb	w5, [x2], #1
	subs	x3, x3, #4
	b.pl	1b
	add	x0, sp, #16
	mov	x1, #16
	bl	type_sub
	ldp	x29, x30, [sp], #32
	ret

// print_udec_sub: x0 unsigned number -> print it in decimal.
print_udec_sub:
	stp	x29, x30, [sp, #-48]!	// digits are built in sp+16 .. sp+48
	add	x2, sp, #48
	mov	x3, x2
	mov	x4, #10
1:	udiv	x5, x0, x4
	msub	x6, x5, x4, x0
	add	w6, w6, #CH_0
	strb	w6, [x3, #-1]!
	mov	x0, x5
	cbnz	x0, 1b
	mov	x0, x3
	sub	x1, x2, x3
	bl	type_sub
	ldp	x29, x30, [sp], #48
	ret
