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
	.equ	F_LENMASK, 0x1f
	.equ	NAME_MAX, 31

	// User area: per-task variables, addressed from UP
	.equ	U_BASE, 0
	.equ	U_STATE, 8
	.equ	U_TOIN, 16		// >in: parse offset into the current line
	.equ	U_NTIB, 24		// #tib: length of the current line
	.equ	U_TIB, 32		// 'tib: address of the current line
	.equ	U_SIZE, 64

	.equ	SRC_TERMINAL, 0
	.equ	SRC_BOOT, 1		// reading the embedded boot files

	.equ	DSTACK_BYTES, 4096
	.equ	RSTACK_BYTES, 4096
	.equ	DICT_BYTES, 1 << 20

	.equ	INSN_NOP, 0xd503201f
	.equ	INSN_MOV_X9_X30, 0xaa1e03e9
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
	message	msg_noname, "missing name\n"
	message	msg_longname, "name too long\n"
	message	msg_noquit, "boot files ended without starting QUIT\n"
	message	msg_colon, ": "

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

	.balign	8
boot_files:
	bootfile "forth/core.fs"
	bootfile "forth/output.fs"
	bootfile "forth/interpreter.fs"	// last: ends by starting the Forth QUIT loop
boot_files_end:

// ---------------------------------------------------------------------------
// Variables and memory

	.data
	.balign	8
var_dp:		.quad	dict_space	// next free byte of the dictionary
var_source:	.quad	SRC_BOOT
var_boot_file:	.quad	boot_files	// table entry of the boot file being loaded
var_boot_pos:	.quad	0		// start of its next line (set by forth_cold)
var_boot_line:	.quad	0		// its line number, for error reports
var_quit:	.quad	0		// xt of the Forth QUIT loop, set by interpreter.fs
var_sp0:	.quad	0		// hardware sp at start-up, restored by abort

	.bss
	.balign	16
dstack:		.space	DSTACK_BYTES
dstack_top:	.space	16		// guard: an underflowing word reads here, then INTERPRET reports it
rstack:		.space	RSTACK_BYTES
rstack_top:
user0:		.space	U_SIZE
	.balign	4096
	.global	dict_space, dict_end
dict_space:	.space	DICT_BYTES	// the platform must make this executable: code fields live here
dict_end:

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
