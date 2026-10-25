// outer.s: start-up, QUIT, ABORT, the bootstrap interpreter and error reporting.
// Included by kernel.s.
//
// The assembly interpreter here only loads the boot files. The end of
// interpreter.fs stores its Forth QUIT loop in 'quit and runs QUIT, which from
// then on enters that loop: the REPL users see is written in Forth.

	.text
	.global	forth_cold
forth_cold:
	ldr	x0, =var_sp0
	mov	x1, sp
	str	x1, [x0]
	ldr	UP, =user0
	mov	x0, #10
	str	x0, [UP, #U_BASE]
	ldr	DSP, =dstack_top
	mov	TOS, #0
	ldr	x0, =boot_files		// start at the first boot file
	ldr	x0, [x0, #BF_START]
	ldr	x1, =var_boot_pos
	str	x0, [x1]
	bl	refill_sub
	b	do_quit

// Reset the return stack and interpret forever: the Forth loop in 'quit once
// the boot files have set it, else the bootstrap interpreter.
do_quit:
	ldr	RSP, =rstack_top
	str	xzr, [UP, #U_STATE]
	ldr	x0, =var_quit
	ldr	x0, [x0]
	cbz	x0, 1f
	ldr	x1, =var_source		// boot files loaded: input is the terminal now
	str	xzr, [x1]
	mov	x8, x0
	br	x8
1:	ldr	IP, =quit_thread
	NEXT

// Reset the data stack and resume QUIT, which reads a fresh line. An error
// while loading the boot files is fatal. Exception handlers return here too.
	.global	do_abort
do_abort:
	ldr	x0, =var_sp0
	ldr	x0, [x0]
	mov	sp, x0
	ldr	DSP, =dstack_top
	mov	TOS, #0
	ldr	x0, =var_source
	ldr	x0, [x0]
	cbz	x0, do_quit
	mov	x0, #1
	b	hal_bye

	.balign	8
quit_thread:
	.quad	interpret, w_branch, quit_thread

// INTERPRET: handle one word of a boot file, moving to the next line at the end
// of one. Execute or compile a word, push or compile a number, or report an error.
// Executed words jump straight to their code, returning to quit_thread.
interpret:
	ldr	x0, =dstack_top
	cmp	DSP, x0
	b.hi	err_underflow
	bl	parse_name_sub
	cbz	x1, 5f
	mov	x24, x0
	mov	x25, x1
	bl	find_sub
	cbz	x0, 2f
	ldr	x2, [UP, #U_STATE]
	cbz	x2, 1f			// interpreting
	cmp	x1, #1
	b.eq	1f			// immediate
	bl	comma_sub
	NEXT
1:	mov	x8, x0
	br	x8
2:	mov	x0, x24
	mov	x1, x25
	bl	number_sub
	cbz	x1, err_undefined
	ldr	x2, [UP, #U_STATE]
	cbz	x2, 3f
	mov	x24, x0
	ldr	x0, =w_lit
	bl	comma_sub
	mov	x0, x24
	bl	comma_sub
	NEXT
3:	PUSH	x0
	NEXT
5:	bl	refill_sub		// end of line
	NEXT

// ---------------------------------------------------------------------------
// Errors. Each prints a message and aborts.

err_undefined:				// x24, x25: the word that was not found
	bl	err_location
	mov	x0, x24
	mov	x1, x25
	bl	type_sub
	ldr	x0, =msg_undefined
	mov	x1, #msg_undefined_len
	b	err_message

err_underflow:
	ldr	x0, =msg_underflow
	mov	x1, #msg_underflow_len
	b	err_located

err_noname:
	ldr	x0, =msg_noname
	mov	x1, #msg_noname_len
	b	err_located

err_noquit:
	ldr	x0, =msg_noquit
	mov	x1, #msg_noquit_len
	b	err_located

err_longname:
	ldr	x0, =msg_longname
	mov	x1, #msg_longname_len

err_located:				// x0, x1: message, printed after the location
	mov	x24, x0
	mov	x25, x1
	bl	err_location
	mov	x0, x24
	mov	x1, x25
err_message:
	bl	type_sub
	b	do_abort

// Print "<file>:<line>: " if the error is in a boot file.
err_location:
	stp	x29, x30, [sp, #-16]!
	ldr	x0, =var_source
	ldr	x0, [x0]
	cbz	x0, 1f
	ldr	x2, =var_boot_file
	ldr	x2, [x2]
	ldr	x0, [x2, #BF_NAME]
	ldr	x1, [x2, #BF_NAMELEN]
	bl	type_sub
	mov	x0, #CH_COLON
	bl	hal_emit
	ldr	x0, =var_boot_line
	ldr	x0, [x0]
	bl	print_udec_sub
	ldr	x0, =msg_colon
	mov	x1, #msg_colon_len
	bl	type_sub
1:	ldp	x29, x30, [sp], #16
	ret
