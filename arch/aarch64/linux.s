// linux.s: platform glue for the hosted kernel, a static AArch64 Linux program
// run under qemu-aarch64 (milestone 2). Bare metal replaces only this file.
//
// HAL contract, called from the kernel under AAPCS64 (may clobber x0-x15, x30):
//   hal_key   -> x0 next input character, or -1 at end of input
//   hal_emit  x0 character ->
//   hal_bye   x0 exit status -> does not return

	.include "macros.s"

	.equ	SYS_IOCTL, 29
	.equ	SYS_READ, 63
	.equ	SYS_WRITE, 64
	.equ	SYS_EXIT_GROUP, 94
	.equ	SYS_MPROTECT, 226

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
	b	forth_cold

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

	.bss
	.balign	8
	.global	linux_args
linux_args:	.space	8			// address of argc, then the argv pointers
saved_termios:	.space	TERMIOS_BYTES
raw_termios:	.space	TERMIOS_BYTES
termios_changed: .space	8
key_buf:	.space	8
emit_buf:	.space	8
