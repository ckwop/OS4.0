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
	ldr	UP, =user0			// the console task: a ring of one
	str	UP, [UP, #U_LINK]
	ldr	x0, =dstack_top
	str	x0, [UP, #U_S0]
	ldr	x0, =rstack_top
	str	x0, [UP, #U_R0]
	ldr	x0, =dstack + STACK_MARGIN
	ldr	x1, =rstack + STACK_MARGIN
	stp	x0, x1, [UP, #U_SLIMIT]
	ldr	x0, =msg_console
	mov	x1, #msg_console_len
	stp	x1, x0, [UP, #U_NAME]
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
	ldr	RSP, [UP, #U_R0]
	str	xzr, [UP, #U_STATE]
	ldr	x0, =var_quit
	ldr	x0, [x0]
	cbz	x0, 1f
	ldr	x1, =var_source		// boot files loaded: input is the terminal now
	str	xzr, [x1]
	isb				// the watchdog counts from here, not from boot
	mrs	x2, cntvct_el0
	ldr	x1, =var_task_since
	str	x2, [x1]
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
	ldr	DSP, [UP, #U_S0]
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
// Errors. Once core.fs has installed THROW and the boot files are loaded, an
// error throws its code to the nearest CATCH. While loading the boot files, it
// prints the file, line and message instead, and the system stops.

err_undefined:				// x24, x25: the word that was not found
	ldr	x0, =var_errname
	stp	x25, x24, [x0]
	mov	x0, #THROW_UNDEFINED
	bl	try_throw
	bl	err_location
	mov	x0, x24
	mov	x1, x25
	bl	type_sub
	ldr	x0, =msg_undefined
	mov	x1, #msg_undefined_len
	b	err_message

err_underflow:
	mov	x0, #THROW_UNDERFLOW
	ldr	x1, =msg_underflow
	mov	x2, #msg_underflow_len
	b	err_code

err_noname:
	mov	x0, #THROW_NONAME
	ldr	x1, =msg_noname
	mov	x2, #msg_noname_len
	b	err_code

err_longname:
	mov	x0, #THROW_LONGNAME
	ldr	x1, =msg_longname
	mov	x2, #msg_longname_len
	b	err_code

err_divzero:
	mov	x0, #THROW_DIVZERO
	ldr	x1, =msg_divzero
	mov	x2, #msg_divzero_len
	b	err_code

err_range:
	mov	x0, #THROW_RANGE
	ldr	x1, =msg_range
	mov	x2, #msg_range_len
	b	err_code

err_overflow:
	mov	x0, #THROW_OVERFLOW
	ldr	x1, =msg_overflow
	mov	x2, #msg_overflow_len
	b	err_code

err_roverflow:
	mov	x0, #THROW_ROVERFLOW
	ldr	x1, =msg_roverflow
	mov	x2, #msg_roverflow_len
	b	err_code

err_runderflow:
	mov	x0, #THROW_RUNDERFLOW
	ldr	x1, =msg_runderflow
	mov	x2, #msg_runderflow_len
	b	err_code

err_dictfull:
	mov	x0, #THROW_DICTFULL
	ldr	x1, =msg_dictfull
	mov	x2, #msg_dictfull_len
	b	err_code

err_noquit:
	ldr	x0, =msg_noquit
	mov	x1, #msg_noquit_len
	b	err_located

err_code:				// x0 throw code; x1, x2 message for a boot-time report
	mov	x24, x1
	mov	x25, x2
	bl	try_throw
	mov	x0, x24
	mov	x1, x25

err_located:				// x0, x1: message, printed after the location
	mov	x24, x0
	mov	x25, x1
	bl	err_location
	mov	x0, x24
	mov	x1, x25
err_message:
	bl	type_sub
	b	do_abort

// try_throw: x0 code -> throw it to the nearest CATCH, as if the running word
// had called THROW; does not return. Returns instead while the boot files are
// loading or before THROW exists.
// Both stacks are first reset to the CATCH frame, as THROW itself would: the
// error may be that a stack overflowed, and THROW must not trip over it.
try_throw:
	ldr	x1, =var_source
	ldr	x1, [x1]
	cbnz	x1, 1f
	ldr	x2, =var_throw
	ldr	x2, [x2]
	cbz	x2, 1f
	ldr	x1, =var_sp0			// Forth keeps nothing on the hardware stack
	ldr	x1, [x1]
	mov	sp, x1
	ldr	x1, [UP, #U_HANDLER]		// frame: enclosing handler, then saved SP@
	cbz	x1, 2f
	mov	RSP, x1
	ldr	x3, [x1, #8]
	add	DSP, x3, #8			// as SP! does
	ldr	TOS, [x3]
2:	PUSH	x0
	mov	x8, x2
	br	x8
1:	ret

// watchdog_sub: x0 interrupted pc -> x0 pc to resume at instead, or 0. Called
// on every timer tick, with interrupts off. If the running task has gone
// var_watchdog counter ticks without pausing, it is sent to watchdog_throw.
// Never in the middle of PAUSE, and only once the system is up.
	.global	watchdog_sub
watchdog_sub:
	ldr	x1, =var_watchdog
	ldr	x1, [x1]
	cbz	x1, 9f
	ldr	x2, =var_source
	ldr	x2, [x2]
	cbnz	x2, 9f
	ldr	x2, =var_throw
	ldr	x2, [x2]
	cbz	x2, 9f
	ldr	x2, =w_pause
	cmp	x0, x2
	b.lo	1f
	ldr	x2, =pause_end
	cmp	x0, x2
	b.lo	9f
1:	ldr	x3, =var_task_since
	ldr	x4, [x3]
	isb
	mrs	x5, cntvct_el0
	sub	x6, x5, x4
	cmp	x6, x1
	b.lo	9f
	str	x5, [x3]			// one throw per stretch
	ldr	x0, =watchdog_throw
	ret
9:	mov	x0, #0
	ret

// The watchdog sent the running task here: it throws from wherever it was.
watchdog_throw:
	mov	x0, #THROW_WATCHDOG
	bl	try_throw
	b	do_abort

// A CPU exception has printed its register dump: throw, or abort if nothing
// can catch it. The Forth registers are as they were at the fault.
	.global	exception_throw
exception_throw:
	ldr	x0, =var_sp0
	ldr	x0, [x0]
	mov	sp, x0
	mov	x0, #THROW_HARDWARE
	bl	try_throw
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
