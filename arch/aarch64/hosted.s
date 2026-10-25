// Hosted kernel stub: a static AArch64 Linux binary run under qemu-aarch64.
// Milestone 2 replaces this with the primitives and the inner and outer interpreters.

	.equ	SYS_WRITE, 64
	.equ	SYS_EXIT, 93
	.equ	STDOUT, 1

	.section .rodata
banner:
	.ascii	"OS 4.0 hosted stub: no Forth yet\n"
	.equ	banner_len, . - banner

	.text
	.global	_start
_start:
	mov	x0, #STDOUT
	adr	x1, banner
	mov	x2, #banner_len
	mov	x8, #SYS_WRITE
	svc	#0

	mov	x0, #0
	mov	x8, #SYS_EXIT
	svc	#0
