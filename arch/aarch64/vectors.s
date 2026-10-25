// vectors.s: AArch64 exception vectors for bare metal. An IRQ from the kernel
// goes to the platform's hal_irq and execution carries on. Any other exception
// prints a register dump on the console, then throws -256 from the faulting
// word, so a bad address typed at the prompt reports itself and the system
// carries on.

	.include "macros.s"

	.equ	SPSR_EL1H_IRQ, 0x345		// EL1 on SP_EL1; IRQs on (the timer tick), D, A, F masked
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
// The table: 16 entries of 128 bytes, in four groups: from this exception level
// on SP_EL0, on SP_ELx, then from a lower level in AArch64 and AArch32. Each
// group has synchronous, IRQ, FIQ and SError entries.

.macro report kind		// save x0 and x1, pass the kind to exc_common
	.balign	128
	msr	tpidr_el1, x1
	ldr	x1, =exc_regs
	str	x0, [x1]
	mrs	x0, tpidr_el1
	str	x0, [x1, #8]
	mov	x0, #\kind
	b	exc_common
.endm

	.text
	.balign	2048
	.global	vectors
vectors:
	report	0			// this level, SP_EL0 (not used: _start selects SP_EL1)
	report	1
	report	2
	report	3
	report	0			// this level, SP_EL1: the kernel
	.balign	128
	b	irq_entry
	report	2
	report	3
	.irp	kind, 0, 1, 2, 3, 0, 1, 2, 3	// lower levels: never expected
	report	\kind
	.endr

// An interrupt: save every register on the current stack, let the platform
// handle it (it may change ELR_EL1 to redirect the interrupted code), return.
irq_entry:
	sub	sp, sp, #256
	stp	x0, x1, [sp, #0]
	stp	x2, x3, [sp, #16]
	stp	x4, x5, [sp, #32]
	stp	x6, x7, [sp, #48]
	stp	x8, x9, [sp, #64]
	stp	x10, x11, [sp, #80]
	stp	x12, x13, [sp, #96]
	stp	x14, x15, [sp, #112]
	stp	x16, x17, [sp, #128]
	stp	x18, x19, [sp, #144]
	stp	x20, x21, [sp, #160]
	stp	x22, x23, [sp, #176]
	stp	x24, x25, [sp, #192]
	stp	x26, x27, [sp, #208]
	stp	x28, x29, [sp, #224]
	str	x30, [sp, #240]
	bl	hal_irq
	ldp	x0, x1, [sp, #0]
	ldp	x2, x3, [sp, #16]
	ldp	x4, x5, [sp, #32]
	ldp	x6, x7, [sp, #48]
	ldp	x8, x9, [sp, #64]
	ldp	x10, x11, [sp, #80]
	ldp	x12, x13, [sp, #96]
	ldp	x14, x15, [sp, #112]
	ldp	x16, x17, [sp, #128]
	ldp	x18, x19, [sp, #144]
	ldp	x20, x21, [sp, #160]
	ldp	x22, x23, [sp, #176]
	ldp	x24, x25, [sp, #192]
	ldp	x26, x27, [sp, #208]
	ldp	x28, x29, [sp, #224]
	ldr	x30, [sp, #240]
	add	sp, sp, #256
	eret

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
	mov	x0, #SPSR_EL1H_IRQ
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
