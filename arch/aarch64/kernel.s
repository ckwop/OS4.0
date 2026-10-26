// kernel.s: the portable AArch64 Forth kernel.
//
// The inner interpreter, the primitives, and the bootstrap outer interpreter and
// compiler. The boot files (forth/*.fs), embedded below, build the rest of the
// system in Forth at start-up. Platform glue (linux.s for the hosted build)
// provides _start, hal_key, hal_emit and hal_bye, and jumps to forth_cold.
//
// This file holds the constants, memory layout and dictionary macros, and
// includes the rest as one assembly unit:
//   outer.s     start-up, QUIT, ABORT, INTERPRET, error reports
//   text.s      input, parsing, lookup, number conversion, output (subroutines)
//   prims.s     primitive words
//   compiler.s  code field handlers and the compiler and parsing words
//
// Threading is direct: an execution token (xt) is the address of machine code.
// A primitive's xt is its code. Every other word starts with an 8-byte code field,
// "<insn>; bl <handler>", so the handler receives the word's body address in x30.
//
// Dictionary header, 8-byte aligned:
//   +0  link to the previous header (0 ends the chain)
//   +8  flags: bit 7 immediate, bit 6 hidden, bits 0-4 name length
//   +9  name, padded to 8 bytes
//   then the xt
//
// Subroutines (*_sub, hal_*) follow AAPCS64: arguments and results in x0-x7; they
// may clobber x0-x15 and x30 and preserve x19-x28. Primitives may use x24-x28
// across subroutine calls.

	.include "macros.s"

	.equ	F_IMMED, 0x80
	.equ	F_HIDDEN, 0x40
	.equ	F_CONLY, 0x20		// compile-only: refused by the interpreter outside definitions
	.equ	F_LENMASK, 0x1f
	.equ	NAME_MAX, 31

	// User area: per-task variables, addressed from UP
	.equ	U_BASE, 0
	.equ	U_STATE, 8
	.equ	U_TOIN, 16		// >in: parse offset into the current line
	.equ	U_NTIB, 24		// #tib: length of the current line
	.equ	U_TIB, 32		// 'tib: address of the current line
	.equ	U_HANDLER, 40		// innermost CATCH frame on the return stack, or 0
	.equ	U_BLK, 48		// block being loaded, or 0 for the terminal
	// Task fields. A task is its user area; tasks.fs makes them.
	.equ	U_LINK, 56		// next task in the round-robin ring
	.equ	U_STATUS, 64		// 0 ready to run, otherwise asleep
	.equ	U_WAKE, 72		// counter value at which an asleep task wakes; 0: only when woken
	.equ	U_SP, 80		// saved data stack pointer while switched out
	.equ	U_RP, 88		// saved return stack pointer
	.equ	U_S0, 96		// data stack pointer when empty
	.equ	U_R0, 104		// return stack pointer when empty
	.equ	U_NAME, 112		// ( addr len ) as 2! stores it: length, then address
	.equ	U_SLIMIT, 128		// lowest safe data stack pointer: below it is overflow
	.equ	U_RLIMIT, 136		// lowest safe return stack pointer (keep after U_SLIMIT)
	.equ	U_SIZE, 256
	.equ	STACK_MARGIN, 16 * 8	// room left below a limit for reporting the overflow

	// THROW codes for errors the kernel detects (standard codes, plus -256)
	.equ	THROW_OVERFLOW, -3
	.equ	THROW_UNDERFLOW, -4
	.equ	THROW_ROVERFLOW, -5
	.equ	THROW_RUNDERFLOW, -6
	.equ	THROW_DICTFULL, -8
	.equ	THROW_DIVZERO, -10
	.equ	THROW_RANGE, -11
	.equ	THROW_UNDEFINED, -13
	.equ	THROW_NONAME, -16
	.equ	THROW_LONGNAME, -19
	.equ	THROW_HARDWARE, -256	// a CPU exception, already reported by its register dump
	.equ	THROW_WATCHDOG, -262	// the task ran too long without pausing

	.equ	SRC_TERMINAL, 0
	.equ	SRC_BOOT, 1		// reading the embedded boot files

	.equ	DSTACK_BYTES, 4096
	.equ	RSTACK_BYTES, 4096

	// The dictionary is a region of RAM the platform hands to forth_cold. Code
	// fields reach their handlers with bl, which spans 128 MiB, so the handlers
	// are reached through trampolines at the start of the region, and the
	// region is capped at 128 MiB.
	.equ	DICT_MAX, (1 << 27) - 4096
	.equ	TRAMPOLINE, 16			// bytes per trampoline: ldr x16, 8; br x16; .quad handler
	.equ	T_DOCOL, 0 * TRAMPOLINE
	.equ	T_DOVAR, 1 * TRAMPOLINE
	.equ	T_DOCON, 2 * TRAMPOLINE
	.equ	T_DODOES, 3 * TRAMPOLINE
	.equ	TRAMPOLINES, 4 * TRAMPOLINE

	.equ	INSN_NOP, 0xd503201f
	.equ	INSN_MOV_X9_X30, 0xaa1e03e9
	.equ	INSN_LDR_X16_8, 0x58000050	// ldr x16, . + 8
	.equ	INSN_BR_X16, 0xd61f0200
	.equ	INSN_BL, 0x94000000

	.equ	CH_LF, 10
	.equ	CH_SPACE, 32
	.equ	CH_COLON, 58
	.equ	CH_HASH, 35
	.equ	CH_DOLLAR, 36
	.equ	CH_PERCENT, 37
	.equ	CH_QUOTE, 39
	.equ	CH_RPAREN, 41
	.equ	CH_MINUS, 45
	.equ	CH_0, 48
	.equ	CH_A_LOWER, 97

// ---------------------------------------------------------------------------
// Messages and the embedded Forth source

	.section .rodata

.macro message label, text
\label:	.ascii	"\text"
	.equ	\label\()_len, . - \label
.endm

	message	msg_undefined, " ?\n"
	message	msg_underflow, "stack underflow\n"
	message	msg_overflow, "stack overflow\n"
	message	msg_roverflow, "return stack overflow\n"
	message	msg_runderflow, "return stack underflow\n"
	message	msg_dictfull, "dictionary full\n"
	message	msg_noname, "missing name\n"
	message	msg_longname, "name too long\n"
	message	msg_divzero, "division by zero\n"
	message	msg_range, "result out of range\n"
	message	msg_aborted, "aborted\n"
	message	msg_noquit, "boot files ended without starting QUIT\n"
	message	msg_colon, ": "
	message	msg_console, "console"

// Boot files: Forth source embedded in the kernel and loaded in this order.
// Each table entry is start, end, name, name length.
	.equ	BF_START, 0
	.equ	BF_END, 8
	.equ	BF_NAME, 16
	.equ	BF_NAMELEN, 24
	.equ	BF_SIZE, 32

.macro bootfile path
	.pushsection .rodata.bootsrc
8:	.incbin	"\path"
9:
	.popsection
	.pushsection .rodata.bootnames
6:	.ascii	"\path"
7:
	.popsection
	.quad	8b, 9b, 6b, 7b - 6b
.endm

// The kernel is assembled once per platform: with HOSTED defined for the Linux
// build, without it for bare metal. Only the drivers differ.
	.balign	8
boot_files:
	bootfile "forth/core.fs"
	bootfile "forth/output.fs"
.ifdef HOSTED
	bootfile "hal/linux-blk.fs"
	bootfile "hal/linux-net.fs"
.else
	bootfile "hal/virtio.fs"
	bootfile "hal/virtio-blk.fs"
	bootfile "hal/virtio-net.fs"
.endif
	bootfile "forth/blocks.fs"
	bootfile "forth/errors.fs"
	bootfile "forth/tasks.fs"
	bootfile "forth/net/eth.fs"
	bootfile "forth/net/arp.fs"
	bootfile "forth/net/ip.fs"
	bootfile "forth/net/icmp.fs"
	bootfile "forth/net/net.fs"
	bootfile "forth/interpreter.fs"	// last: ends by starting the Forth QUIT loop
boot_files_end:

// ---------------------------------------------------------------------------
// Variables and memory

	.data
	.balign	8
var_dp:		.quad	0		// next free byte of the dictionary
var_dict_end:	.quad	0		// where the dictionary ends
var_tramps:	.quad	0		// the handler trampolines, at the start of the dictionary
var_source:	.quad	SRC_BOOT
var_boot_file:	.quad	boot_files	// table entry of the boot file being loaded
var_boot_pos:	.quad	0		// start of its next line (set by forth_cold)
var_boot_line:	.quad	0		// its line number, for error reports
var_quit:	.quad	0		// xt of the Forth QUIT loop, set by interpreter.fs
var_throw:	.quad	0		// xt of THROW, set by core.fs; kernel errors throw through it
var_errname:	.quad	0, 0		// ( addr len ) as 2! stores it: the word an error is about
var_task_since:	.quad	0		// counter value when the running task was switched in
var_watchdog:	.quad	0		// counter ticks a task may run without pausing; 0: off
var_sp0:	.quad	0		// hardware sp at start-up, restored by abort

	.bss
	.balign	16
dstack:		.space	DSTACK_BYTES
dstack_top:	.space	16		// guard: an underflowing word reads here, then INTERPRET reports it
rstack:		.space	RSTACK_BYTES
rstack_top:
user0:		.space	U_SIZE

// CHECK_STACKS: throw if either stack has grown past its limit. In every colon
// call and backward branch, so runaway recursion and runaway loops are caught
// before they overwrite the task's user area or the other stack.
.macro CHECK_STACKS
	ldp	x9, x10, [UP, #U_SLIMIT]
	cmp	DSP, x9
	b.lo	err_overflow
	cmp	RSP, x10
	b.lo	err_roverflow
.endm

// ---------------------------------------------------------------------------
// Dictionary. Each word: header, then the code its xt points at. The link
// chain runs through every file below, so they assemble as one unit.

	.set	link, 0

.macro defcode name, label, flags=0
	.balign	8
\label\()_nt:
	.quad	link
	.set	link, \label\()_nt
	.byte	\flags + 9f - 8f
8:	.ascii	"\name"
9:	.balign	8
\label:
.endm

.macro defword name, label, flags=0
	defcode	"\name", \label, \flags
	nop
	bl	docol
.endm

.macro defconst name, label, value
	defcode	"\name", \label
	str	TOS, [DSP, #-8]!
	ldr	TOS, =\value
	NEXT
.endm

.macro defuser name, label, offset
	defcode	"\name", \label
	PUSH	UP
	add	TOS, TOS, #\offset
	NEXT
.endm

	.include "outer.s"
	.include "text.s"
	.include "prims.s"
	.include "compiler.s"

	.data
	.balign	8
var_latest:	.quad	link			// newest header: the last one above
