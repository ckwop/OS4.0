// vectors.s: AArch64 exception vectors for bare metal. Any exception prints a
// register dump on the console, then throws -256 from the faulting word, so a
// bad address typed at the prompt reports itself and the system carries on.

	.include "macros.s"

	.equ	SPSR_EL1H_MASKED, 0x3c5		// EL1 on SP_EL1, interrupts masked
	.equ	REG_SP, 31			// slot of sp in exc_regs
	.equ	CH_LF, 10
	.equ	CH_SPACE, 32
	.equ	CH_EQUALS, 61
	.equ	CH_X, 120

	.section .rodata
msg_exception:	.ascii	"\nexception: "
	.equ	msg_exception_len, . - msg_exception
msg_esr:	.ascii	"ESR="
msg_elr:	.ascii	" ELR="
msg_far:	.ascii	" FAR="
msg_spsr:	.ascii	" SPSR="
msg_sp:		.ascii	"sp="
kind_names:	.ascii	"synchronous"		// indexed by the vector's low 2 bits
		.ascii	"IRQ"
		.ascii	"FIQ"
		.ascii	"SError"
kind_offsets:	.byte	0, 11, 14, 17, 23

// ---------------------------------------------------------------------------
// The table: 16 entries of 128 bytes. Each saves x0 and x1, then passes the
// exception kind (synchronous, IRQ, FIQ, SError) to exc_common in x0.

	.text
	.balign	2048
	.global	vectors
vectors:
	.irp	kind, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3
	.balign	128
	msr	tpidr_el1, x1
	ldr	x1, =exc_regs
	str	x0, [x1]
	mrs	x0, tpidr_el1
	str	x0, [x1, #8]
	mov	x0, #\kind
	b	exc_common
	.endr

exc_common:				// x0 kind, x1 exc_regs; x2-x30 and sp still live
	stp	x2, x3, [x1, #16]
	stp	x4, x5, [x1, #32]
	stp	x6, x7, [x1, #48]
	stp	x8, x9, [x1, #64]
	stp	x10, x11, [x1, #80]
	stp	x12, x13, [x1, #96]
	stp	x14, x15, [x1, #112]
	stp	x16, x17, [x1, #128]
	stp	x18, x19, [x1, #144]
	stp	x20, x21, [x1, #160]
	stp	x22, x23, [x1, #176]
	stp	x24, x25, [x1, #192]
	stp	x26, x27, [x1, #208]
	stp	x28, x29, [x1, #224]
	str	x30, [x1, #240]
	mov	x2, sp
	str	x2, [x1, #(8 * REG_SP)]
	ldr	x2, =exc_stack_top		// the faulting stack may be the problem
	mov	sp, x2
	ldr	x2, =exc_busy			// a fault while reporting one: give up
	ldr	x3, [x2]
	cbnz	x3, 9f
	mov	x3, #1
	str	x3, [x2]
	mov	x24, x0

	ldr	x0, =msg_exception		// "exception: <kind>"
	mov	x1, #msg_exception_len
	bl	type_sub
	ldr	x2, =kind_offsets
	ldrb	w3, [x2, x24]
	add	x4, x24, #1
	ldrb	w4, [x2, x4]
	ldr	x0, =kind_names
	add	x0, x0, x3
	sub	x1, x4, x3
	bl	type_sub
	mov	x0, #CH_LF
	bl	hal_emit

	ldr	x0, =msg_esr			// syndrome, return address, fault address, saved PSTATE
	mov	x1, #4
	bl	type_sub
	mrs	x0, esr_el1
	bl	print_hex_sub
	ldr	x0, =msg_elr
	mov	x1, #5
	bl	type_sub
	mrs	x0, elr_el1
	bl	print_hex_sub
	ldr	x0, =msg_far
	mov	x1, #5
	bl	type_sub
	mrs	x0, far_el1
	bl	print_hex_sub
	ldr	x0, =msg_spsr
	mov	x1, #6
	bl	type_sub
	mrs	x0, spsr_el1
	bl	print_hex_sub
	mov	x0, #CH_LF
	bl	hal_emit

	mov	x25, #0				// x0 ... x30 and sp, four to a line
1:	cmp	x25, #REG_SP
	b.eq	2f
	mov	x0, #CH_X
	bl	hal_emit
	mov	x0, x25
	bl	print_udec_sub
	mov	x0, #CH_EQUALS
	bl	hal_emit
	b	3f
2:	ldr	x0, =msg_sp
	mov	x1, #3
	bl	type_sub
3:	ldr	x0, =exc_regs
	ldr	x0, [x0, x25, lsl #3]
	bl	print_hex_sub
	and	x0, x25, #3
	cmp	x0, #3
	mov	x0, #CH_SPACE
	mov	x1, #CH_LF
	csel	x0, x1, x0, eq
	bl	hal_emit
	add	x25, x25, #1
	cmp	x25, #REG_SP
	b.ls	1b

	ldr	x0, =exc_busy
	str	xzr, [x0]
	ldr	x0, =exception_throw		// resume as if the faulting word had thrown
	msr	elr_el1, x0
	mov	x0, #SPSR_EL1H_MASKED
	msr	spsr_el1, x0
	eret
9:	wfe
	b	9b

	.bss
	.balign	16
exc_regs:	.space	8 * 32
exc_busy:	.space	8
exc_stack:	.space	4096
exc_stack_top:
