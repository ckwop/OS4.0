// linux.s: platform glue for the hosted kernel, a static AArch64 Linux program
// run under qemu-aarch64 (milestone 2). Bare metal replaces only this file.
//
// HAL contract, called from the kernel under AAPCS64 (may clobber x0-x15, x30):
//   hal_key        -> x0 next input character, or -1 at end of input
//   hal_key_ready  -> x0 nonzero if a character is waiting, or input has ended
//   hal_emit       x0 character ->
//   hal_idle       wait a little: nothing can run
//   hal_bye        x0 exit status -> does not return
// The timer tick is SIGALRM, every 10 ms, which runs the watchdog.

	.include "macros.s"

	.equ	SYS_IOCTL, 29
	.equ	SYS_READ, 63
	.equ	SYS_WRITE, 64
	.equ	SYS_PPOLL, 73
	.equ	SYS_EXIT_GROUP, 94
	.equ	SYS_NANOSLEEP, 101
	.equ	SYS_SETITIMER, 103
	.equ	SYS_RT_SIGACTION, 134
	.equ	SYS_RT_SIGRETURN, 139
	.equ	SYS_MPROTECT, 226

	.equ	SIGILL, 4
	.equ	SIGBUS, 7
	.equ	SIGSEGV, 11
	.equ	SIGALRM, 14
	.equ	SA_FLAGS, 0x14000004		// SA_RESTART | SA_RESTORER | SA_SIGINFO
	.equ	ITIMER_REAL, 0
	.equ	TICK_USEC, 10000
	.equ	UC_FAULT, 176			// fault_address in the ucontext of a signal frame
	.equ	UC_PC, 440			// pc
	.equ	POLLIN, 1

	.equ	PROT_RWX, 7
	.equ	TCGETS, 0x5401
	.equ	TCSETS, 0x5402
	.equ	TERMIOS_LFLAG, 12		// offset of c_lflag in struct termios
	.equ	TERMIOS_VTIME, 17 + 5		// c_cc[VTIME]
	.equ	TERMIOS_VMIN, 17 + 6		// c_cc[VMIN]
	.equ	ICANON, 0x2
	.equ	ECHO, 0x8
	.equ	TERMIOS_BYTES, 64		// struct termios is 36 bytes; leave room

	.text
	.global	_start
_start:
	ldr	x0, =linux_args			// the kernel put argc and argv at sp
	mov	x1, sp
	str	x1, [x0]
	// Code fields are written into the dictionary at run time, so it must be executable.
	ldr	x0, =dict_space
	ldr	x1, =dict_end
	sub	x1, x1, x0
	mov	x2, #PROT_RWX
	mov	x8, #SYS_MPROTECT
	svc	#0
	cbz	x0, 1f
	mov	x0, #2
	b	hal_bye
1:	bl	terminal_raw
	bl	faults_init
	bl	timer_init
	b	forth_cold

// A bad memory access or instruction is reported, then the faulting word
// throws -256, as on bare metal.
faults_init:
	stp	x29, x30, [sp, #-16]!
	ldr	x1, =fault_action
	ldr	x0, =fault_handler
	str	x0, [x1]
	ldr	x0, =SA_FLAGS
	str	x0, [x1, #8]
	ldr	x0, =alarm_restorer
	str	x0, [x1, #16]
	str	xzr, [x1, #24]
	mov	x0, #SIGSEGV
	bl	1f
	mov	x0, #SIGBUS
	bl	1f
	mov	x0, #SIGILL
	bl	1f
	ldp	x29, x30, [sp], #16
	ret
1:	ldr	x1, =fault_action
	mov	x2, #0
	mov	x3, #8
	mov	x8, #SYS_RT_SIGACTION
	svc	#0
	ret

// x0 signal, x2 ucontext. Print "exception: signal 11 at <address>", then
// resume the faulting code in exception_throw.
fault_handler:
	stp	x29, x30, [sp, #-32]!
	stp	x0, x2, [sp, #16]
	ldr	x0, =msg_fault
	mov	x1, #msg_fault_len
	bl	type_sub
	ldr	x0, [sp, #16]
	bl	print_udec_sub
	ldr	x0, =msg_fault_at
	mov	x1, #msg_fault_at_len
	bl	type_sub
	ldr	x2, [sp, #24]
	ldr	x0, [x2, #UC_FAULT]
	bl	print_hex_sub
	mov	x0, #10
	bl	hal_emit
	ldr	x2, [sp, #24]
	ldr	x0, =exception_throw
	str	x0, [x2, #UC_PC]
	ldp	x29, x30, [sp], #32
	ret

// Deliver SIGALRM every tick. Interrupted system calls restart.
timer_init:
	ldr	x1, =alarm_action
	ldr	x0, =alarm_handler
	str	x0, [x1]
	ldr	x0, =SA_FLAGS
	str	x0, [x1, #8]
	ldr	x0, =alarm_restorer
	str	x0, [x1, #16]
	str	xzr, [x1, #24]			// block nothing extra
	mov	x0, #SIGALRM
	mov	x2, #0
	mov	x3, #8
	mov	x8, #SYS_RT_SIGACTION
	svc	#0
	mov	x0, #ITIMER_REAL
	ldr	x1, =alarm_interval
	mov	x2, #0
	mov	x8, #SYS_SETITIMER
	svc	#0
	ret

// The tick: x2 points at the ucontext. If the watchdog says so, the interrupted
// code resumes in watchdog_throw instead. Its Forth registers are intact.
alarm_handler:
	stp	x29, x30, [sp, #-32]!
	str	x2, [sp, #16]
	ldr	x0, [x2, #UC_PC]
	bl	watchdog_sub
	cbz	x0, 1f
	ldr	x2, [sp, #16]
	str	x0, [x2, #UC_PC]
1:	ldp	x29, x30, [sp], #32
	ret

alarm_restorer:
	mov	x8, #SYS_RT_SIGRETURN
	svc	#0

	.global	hal_key_ready
hal_key_ready:
	ldr	x0, =poll_stdin
	str	wzr, [x0]			// fd 0
	mov	w1, #POLLIN
	str	w1, [x0, #4]			// events POLLIN, revents 0
	mov	x1, #1
	ldr	x2, =zero_time
	mov	x3, #0
	mov	x4, #8
	mov	x8, #SYS_PPOLL
	svc	#0
	cmp	x0, #0
	cset	x0, gt
	ret

	.global	hal_idle
hal_idle:
	ldr	x0, =idle_time
	mov	x1, #0
	mov	x8, #SYS_NANOSLEEP
	svc	#0
	ret

// If stdin is a terminal, turn off its line editing and echo. The Forth echoes
// input itself, as it must on a serial console, so both behave the same.
terminal_raw:
	mov	x0, #0
	mov	x1, #TCGETS
	ldr	x2, =saved_termios
	mov	x8, #SYS_IOCTL
	svc	#0
	cbnz	x0, 2f				// not a terminal
	ldr	x0, =saved_termios
	ldr	x1, =raw_termios
	mov	x2, #0
1:	ldr	x3, [x0, x2]
	str	x3, [x1, x2]
	add	x2, x2, #8
	cmp	x2, #TERMIOS_BYTES
	b.lo	1b
	ldr	w3, [x1, #TERMIOS_LFLAG]
	mov	w4, #(ICANON | ECHO)
	bic	w3, w3, w4
	str	w3, [x1, #TERMIOS_LFLAG]
	mov	w4, #1
	strb	w4, [x1, #TERMIOS_VMIN]		// read returns after each character
	strb	wzr, [x1, #TERMIOS_VTIME]
	mov	x0, #0
	mov	x2, x1
	mov	x1, #TCSETS
	mov	x8, #SYS_IOCTL
	svc	#0
	ldr	x0, =termios_changed
	mov	x1, #1
	str	x1, [x0]
2:	ret

	.global	hal_key
hal_key:
	mov	x0, #0
	ldr	x1, =key_buf
	mov	x2, #1
	mov	x8, #SYS_READ
	svc	#0
	cmp	x0, #1
	b.ne	1f				// end of input or error
	ldr	x1, =key_buf
	ldrb	w0, [x1]
	ret
1:	mov	x0, #-1
	ret

	.global	hal_emit
hal_emit:
	ldr	x1, =emit_buf
	strb	w0, [x1]
	mov	x0, #1
	mov	x2, #1
	mov	x8, #SYS_WRITE
	svc	#0
	ret

	.global	hal_bye
hal_bye:
	mov	x9, x0
	ldr	x0, =termios_changed
	ldr	x0, [x0]
	cbz	x0, 1f
	mov	x0, #0				// restore the terminal
	mov	x1, #TCSETS
	ldr	x2, =saved_termios
	mov	x8, #SYS_IOCTL
	svc	#0
1:	mov	x0, x9
	mov	x8, #SYS_EXIT_GROUP
	svc	#0

	.section .rodata
msg_fault:	.ascii	"\nexception: signal "
	.equ	msg_fault_len, . - msg_fault
msg_fault_at:	.ascii	" at "
	.equ	msg_fault_at_len, . - msg_fault_at

	.data
	.balign	8
alarm_interval:	.quad	0, TICK_USEC, 0, TICK_USEC	// interval, then first expiry: sec, usec
zero_time:	.quad	0, 0				// timespec: do not wait
idle_time:	.quad	0, 1000000			// timespec: 1 ms

	.bss
	.balign	8
alarm_action:	.space	32			// struct sigaction
fault_action:	.space	32
poll_stdin:	.space	8			// struct pollfd
	.global	linux_args
linux_args:	.space	8			// address of argc, then the argv pointers
saved_termios:	.space	TERMIOS_BYTES
raw_termios:	.space	TERMIOS_BYTES
termios_changed: .space	8
key_buf:	.space	8
emit_buf:	.space	8
