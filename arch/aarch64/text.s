// text.s: reading the boot files, parsing, dictionary lookup, number conversion
// and text output, as subroutines for the bootstrap interpreter and compiler.
// Included by kernel.s.

	.text
	.global	type_sub, print_hex_sub, print_udec_sub	// for platform code, e.g. exception reports

// refill_sub: make the next line of the boot files current, moving on to the
// next file at the end of one. Running out is an error: the last file must
// start the Forth QUIT loop.
refill_sub:
	ldr	x5, =var_boot_file
	ldr	x0, =var_boot_pos
1:	ldr	x6, [x5]
	ldr	x1, [x0]
	ldr	x2, [x6, #BF_END]
	cmp	x1, x2
	b.lo	2f
	add	x6, x6, #BF_SIZE	// this file is done
	ldr	x7, =boot_files_end
	cmp	x6, x7
	b.hs	err_noquit
	str	x6, [x5]
	ldr	x1, [x6, #BF_START]
	str	x1, [x0]
	ldr	x3, =var_boot_line
	str	xzr, [x3]
	b	1b
2:	str	x1, [UP, #U_TIB]
	mov	x3, x1
3:	cmp	x3, x2
	b.hs	4f
	ldrb	w4, [x3]
	cmp	w4, #CH_LF
	b.eq	4f
	add	x3, x3, #1
	b	3b
4:	sub	x4, x3, x1
	str	x4, [UP, #U_NTIB]
	add	x3, x3, #1
	str	x3, [x0]
	ldr	x0, =var_boot_line
	ldr	x1, [x0]
	add	x1, x1, #1
	str	x1, [x0]
	str	xzr, [UP, #U_TOIN]
	ret

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
