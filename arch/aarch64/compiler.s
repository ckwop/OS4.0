// compiler.s: code field handlers and the words that build the dictionary,
// parse input and run the outer loop. Included by kernel.s.

	.text

// comma_sub: x0 cell -> compile it at the end of the dictionary.
comma_sub:
	ldr	x1, =var_dp
	ldr	x2, [x1]
	str	x0, [x2], #8
	str	x2, [x1]
	ret

// header_sub: x0 name, x1 length -> lay down a dictionary header and link it in.
// The dictionary pointer is left at the new word's xt.
header_sub:
	cbz	x1, err_noname
	cmp	x1, #NAME_MAX
	b.hi	err_longname
	ldr	x2, =var_dp
	ldr	x3, [x2]
	add	x3, x3, #7
	and	x3, x3, #-8
	ldr	x4, =var_latest
	ldr	x5, [x4]
	str	x5, [x3]
	str	x3, [x4]
	strb	w1, [x3, #8]
	add	x6, x3, #9
	mov	x7, #0
1:	cmp	x7, x1
	b.hs	2f
	ldrb	w8, [x0, x7]
	strb	w8, [x6, x7]
	add	x7, x7, #1
	b	1b
2:	add	x6, x6, x1
	add	x6, x6, #7
	and	x6, x6, #-8
	str	x6, [x2]
	ret

// write_cf_sub: x0 first instruction, x1 handler, x2 address (8-byte aligned) ->
// write the code field "<insn>; bl <handler>" and sync it to instruction fetch.
write_cf_sub:
	str	w0, [x2]
	add	x3, x2, #4
	sub	x3, x1, x3
	asr	x3, x3, #2
	and	x3, x3, #0x3ffffff
	movz	w4, #(INSN_BL >> 16), lsl #16
	orr	w3, w3, w4
	str	w3, [x2, #4]
	SYNC_ICACHE x2
	ret

// ---------------------------------------------------------------------------
// Code field handlers. x30 holds the body address of the word being run.

docol:					// colon definition: run the thread in the body
	RPUSH	IP
	mov	IP, x30
	NEXT

dovar:					// CREATE, VARIABLE: push the body address
	PUSH	x30
	NEXT

docon:					// CONSTANT: push the value held in the body
	str	TOS, [DSP, #-8]!
	ldr	TOS, [x30]
	NEXT

// A word built by CREATE ... DOES> jumps to the "mov x9, x30; bl dodoes" that
// DOES> compiled into its defining word. x9 is the child's body; x30 is the
// thread that follows DOES>.
dodoes:
	PUSH	x9
	RPUSH	IP
	mov	IP, x30
	NEXT

// ---- Variables and constants used by core.fs

	defconst "dp", w_dp, var_dp		// ( -- addr ) dictionary pointer
	defconst "latest", w_latest, var_latest	// ( -- addr ) newest header
	defuser	"base", w_base, U_BASE		// ( -- addr )
	defuser	"state", w_state, U_STATE	// ( -- addr ) true while compiling
	defuser	">in", w_toin, U_TOIN		// ( -- addr )
	defuser	"#tib", w_ntib, U_NTIB		// ( -- addr )
	defuser	"'tib", w_ticktib, U_TIB	// ( -- addr )
	defconst "docol", w_docol, docol	// ( -- addr ) code field handlers, for CF,
	defconst "dovar", w_dovar, dovar
	defconst "docon", w_docon, docon

// ---- Compiler

	defcode	",", w_comma			// ( x -- )
	POP	x0
	bl	comma_sub
	NEXT

	defcode	"header", w_header		// ( addr len -- ) lay down a header for that name
	POP	x1
	POP	x0
	bl	header_sub
	NEXT

	defcode	"cf,", w_cfcomma		// ( handler -- ) compile the code field "nop; bl handler"
	POP	x1
	ldr	w0, =INSN_NOP
compile_cf:
	ldr	x2, =var_dp
	ldr	x2, [x2]
	bl	write_cf_sub
	ldr	x0, =var_dp
	ldr	x1, [x0]
	add	x1, x1, #8
	str	x1, [x0]
	NEXT

	defcode	"does-cf,", w_doescfcomma	// ( -- ) compile "mov x9, x30; bl dodoes", for DOES>
	ldr	w0, =INSN_MOV_X9_X30
	ldr	x1, =dodoes
	b	compile_cf

	// ( -- ) ( R: ip -- ) end the defining word, pointing the newest word's code
	// field at the DOES> code that follows in the thread.
	defcode	"(does>)", w_pdoes
	ldr	x0, =var_latest
	ldr	x0, [x0]
	ldrb	w1, [x0, #8]
	and	x1, x1, #F_LENMASK
	add	x2, x0, x1
	add	x2, x2, #(9 + 7)
	and	x2, x2, #-8
	ldr	w0, =INSN_NOP
	mov	x1, IP
	bl	write_cf_sub
	RPOP	IP
	NEXT

	defcode	"immediate", w_immediate	// ( -- ) mark the newest word immediate
	mov	x1, #F_IMMED
	b	set_flag

	defcode	"hide", w_hide			// ( -- ) hide the newest word from FIND
	mov	x1, #F_HIDDEN
set_flag:
	ldr	x0, =var_latest
	ldr	x0, [x0]
	ldrb	w2, [x0, #8]
	orr	w2, w2, w1
	strb	w2, [x0, #8]
	NEXT

	defcode	"reveal", w_reveal		// ( -- ) make the newest word findable
	ldr	x0, =var_latest
	ldr	x0, [x0]
	ldrb	w2, [x0, #8]
	and	w2, w2, #~F_HIDDEN
	strb	w2, [x0, #8]
	NEXT

	defcode	"[", w_lbracket, F_IMMED	// ( -- ) interpret
	str	xzr, [UP, #U_STATE]
	NEXT

	defcode	"]", w_rbracket			// ( -- ) compile
	mov	x0, #-1
	str	x0, [UP, #U_STATE]
	NEXT

// ---- Parsing and lookup

	defcode	"parse-name", w_parsename	// ( "name" -- addr len )
	bl	parse_name_sub
	PUSH	x0
	PUSH	x1
	NEXT

	defcode	"parse", w_parse		// ( char "ccc<char>" -- addr len )
	mov	x0, TOS
	bl	parse_sub
	mov	TOS, x0
	PUSH	x1
	NEXT

	defcode	"find-word", w_findword		// ( addr len -- 0 | xt 1 | xt -1 ) 1 if immediate
	POP	x1
	mov	x0, TOS
	bl	find_sub
	cbz	x0, 1f
	mov	TOS, x0
	PUSH	x1
	NEXT
1:	mov	TOS, #0
	NEXT

	defcode	"parse-find", w_parsefind	// ( "name" -- xt 1 | xt -1 ) aborts if not found
	bl	parse_name_sub
	cbz	x1, err_noname
	mov	x24, x0
	mov	x25, x1
	bl	find_sub
	cbz	x0, err_undefined
	PUSH	x0
	PUSH	x1
	NEXT

	defcode	"\\", w_backslash, F_IMMED	// ( -- ) comment to the end of the line
	ldr	x0, [UP, #U_NTIB]
	str	x0, [UP, #U_TOIN]
	NEXT

	defcode	"(", w_paren, F_IMMED		// ( -- ) comment to the next )
	mov	x0, #CH_RPAREN
	bl	parse_sub
	NEXT

// ---- Defining colon words, and the outer loop

	defword	":", w_colon			// ( "name" -- ) start a colon definition
	.quad	w_parsename, w_header, w_docol, w_cfcomma, w_hide, w_rbracket, w_exit

	defword	";", w_semicolon, F_IMMED	// ( -- ) end a colon definition
	.quad	w_lit, w_exit, w_comma, w_reveal, w_lbracket, w_exit

	defcode	"quit", w_quit			// ( -- ) ( R: i*x -- ) back to the outer interpreter
	b	do_quit

	defcode	"abort", w_abort		// ( i*x -- ) empty the stacks; next line
	b	do_abort
