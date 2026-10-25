// macros.s: register names and macros shared by the kernel and platform glue.

// Forth machine state lives in callee-saved registers, so C code preserves it.
IP	.req	x19		// instruction pointer: the next cell of the current thread
DSP	.req	x20		// data stack pointer, grows down (TOS is cached, not in memory)
RSP	.req	x21		// return stack pointer, grows down
TOS	.req	x22		// top of the data stack
TOSW	.req	w22		// low 32 bits of TOS, for byte loads and stores
UP	.req	x23		// user area of the current task

// NEXT: fetch the next xt from the thread and jump to its code.
.macro NEXT
	ldr	x8, [IP], #8
	br	x8
.endm

// PUSH reg ( -- x ): spill TOS to memory; reg becomes the new TOS.
.macro PUSH reg
	str	TOS, [DSP, #-8]!
	mov	TOS, \reg
.endm

// POP reg ( x -- ): move TOS into reg and reload TOS from memory.
.macro POP reg
	mov	\reg, TOS
	ldr	TOS, [DSP], #8
.endm

.macro RPUSH reg
	str	\reg, [RSP, #-8]!
.endm

.macro RPOP reg
	ldr	\reg, [RSP], #8
.endm

// TOLOWER reg, tmp: fold an ASCII upper-case letter in reg to lower case.
.macro TOLOWER reg, tmp
	sub	\tmp, \reg, #65
	cmp	\tmp, #25
	add	\tmp, \reg, #32
	csel	\reg, \tmp, \reg, ls
.endm

// VIRT_TO_PHYS reg, tmp: translate the mapped virtual address in reg to its
// physical address, using the MMU's own stage 1 lookup.
.macro VIRT_TO_PHYS reg, tmp
	at	s1e1r, \reg
	isb
	mrs	\tmp, par_el1
	and	\tmp, \tmp, #0x0000fffffffff000
	and	\reg, \reg, #0xfff
	orr	\reg, \reg, \tmp
.endm

// SYNC_ICACHE addr: make code just written at addr visible to instruction fetch.
// Covers one cache line, so the code written must not cross a 16-byte boundary.
.macro SYNC_ICACHE addr
	dc	cvau, \addr
	dsb	ish
	ic	ivau, \addr
	dsb	ish
	isb
.endm
