// prims.s: primitive words: inner interpreter, stack, arithmetic, memory,
// counted loops and the terminal. Included by kernel.s.

	.text

// ---- Inner interpreter

	defcode	"exit", w_exit, F_CONLY			// ( -- ) ( R: ip -- )
	RPOP	IP
	NEXT

	defcode	"lit", w_lit, F_CONLY			// ( -- x ) push the cell that follows
	str	TOS, [DSP, #-8]!
	ldr	TOS, [IP], #8
	NEXT

	defcode	"branch", w_branch, F_CONLY		// ( -- ) jump to the address that follows
	CHECK_STACKS
	ldr	IP, [IP]
	NEXT

	defcode	"0branch", w_zbranch, F_CONLY		// ( flag -- ) jump if flag is zero
	CHECK_STACKS
	POP	x0
	cbz	x0, 1f
	add	IP, IP, #8
	NEXT
1:	ldr	IP, [IP]
	NEXT

	defcode	"execute", w_execute		// ( i*x xt -- j*x )
	POP	x8
	br	x8

// ---- Stack

	defcode	"dup", w_dup			// ( x -- x x )
	str	TOS, [DSP, #-8]!
	NEXT

	defcode	"drop", w_drop			// ( x -- )
	ldr	TOS, [DSP], #8
	NEXT

	defcode	"swap", w_swap			// ( a b -- b a )
	ldr	x0, [DSP]
	str	TOS, [DSP]
	mov	TOS, x0
	NEXT

	defcode	"over", w_over			// ( a b -- a b a )
	ldr	x0, [DSP]
	PUSH	x0
	NEXT

	defcode	">r", w_tor, F_CONLY			// ( x -- ) ( R: -- x )
	RPUSH	TOS
	ldr	TOS, [DSP], #8
	NEXT

	defcode	"r>", w_rfrom, F_CONLY			// ( -- x ) ( R: x -- )
	str	TOS, [DSP, #-8]!
	RPOP	TOS
	NEXT

	defcode	"r@", w_rfetch, F_CONLY			// ( -- x ) ( R: x -- x )
	str	TOS, [DSP, #-8]!
	ldr	TOS, [RSP]
	NEXT

	defcode	"depth", w_depth		// ( -- n )
	ldr	x0, [UP, #U_S0]
	sub	x0, x0, DSP
	asr	x0, x0, #3
	PUSH	x0
	NEXT

	defcode	"pick", w_pick			// ( xu ... x0 u -- xu ... x0 xu )
	ldr	TOS, [DSP, TOS, lsl #3]
	NEXT

// Stack pointers, for CATCH and THROW. SP@ spills TOS and returns where it went,
// so SP! of that address restores the stack exactly as it was before SP@.

	defcode	"sp@", w_spfetch		// ( -- addr )
	str	TOS, [DSP, #-8]!
	mov	TOS, DSP
	NEXT

	defcode	"sp!", w_spstore, F_CONLY		// ( addr -- i*x ) the stack as it was at SP@
	add	DSP, TOS, #8
	ldr	TOS, [TOS]
	NEXT

	defcode	"rp@", w_rpfetch		// ( -- addr )
	PUSH	RSP
	NEXT

	defcode	"rp!", w_rpstore, F_CONLY		// ( addr -- ) ( R: i*x -- j*x )
	POP	RSP
	NEXT

// ---- Arithmetic and logic

	defcode	"+", w_plus			// ( a b -- a+b )
	ldr	x0, [DSP], #8
	add	TOS, x0, TOS
	NEXT

	defcode	"-", w_minus			// ( a b -- a-b )
	ldr	x0, [DSP], #8
	sub	TOS, x0, TOS
	NEXT

	defcode	"*", w_star			// ( a b -- a*b )
	ldr	x0, [DSP], #8
	mul	TOS, x0, TOS
	NEXT

	defcode	"/mod", w_slashmod		// ( n1 n2 -- rem quot ) floored, as gforth
	cbz	TOS, err_divzero
	ldr	x0, [DSP]
	sdiv	x1, x0, TOS
	msub	x2, x1, TOS, x0
	cbz	x2, 1f
	eor	x3, x2, TOS
	tbz	x3, #63, 1f			// remainder has the divisor's sign
	sub	x1, x1, #1
	add	x2, x2, TOS
1:	str	x2, [DSP]
	mov	TOS, x1
	NEXT

	defcode	"um*", w_umstar			// ( u1 u2 -- ud )
	ldr	x0, [DSP]
	mul	x1, x0, TOS
	umulh	TOS, x0, TOS
	str	x1, [DSP]
	NEXT

	// ( ud u -- urem uquot ) 128 by 64 bit restoring division. The high cell
	// of ud must be less than u, so the quotient fits in one cell.
	defcode	"um/mod", w_umslashmod
	cbz	TOS, err_divzero
	ldr	x1, [DSP]			// high
	cmp	x1, TOS
	b.hs	err_range
	add	DSP, DSP, #8
	ldr	x0, [DSP]			// low
	mov	x3, #64
1:	lsr	x4, x1, #63
	extr	x1, x1, x0, #63
	lsl	x0, x0, #1
	cbnz	x4, 2f
	cmp	x1, TOS
	b.lo	3f
2:	sub	x1, x1, TOS
	orr	x0, x0, #1
3:	subs	x3, x3, #1
	b.ne	1b
	str	x1, [DSP]
	mov	TOS, x0
	NEXT

	defcode	"and", w_and			// ( a b -- a&b )
	ldr	x0, [DSP], #8
	and	TOS, x0, TOS
	NEXT

	defcode	"or", w_or			// ( a b -- a|b )
	ldr	x0, [DSP], #8
	orr	TOS, x0, TOS
	NEXT

	defcode	"xor", w_xor			// ( a b -- a^b )
	ldr	x0, [DSP], #8
	eor	TOS, x0, TOS
	NEXT

	defcode	"invert", w_invert		// ( x -- ~x )
	mvn	TOS, TOS
	NEXT

	defcode	"lshift", w_lshift		// ( x u -- x<<u )
	ldr	x0, [DSP], #8
	lsl	TOS, x0, TOS
	NEXT

	defcode	"rshift", w_rshift		// ( x u -- x>>u ) logical
	ldr	x0, [DSP], #8
	lsr	TOS, x0, TOS
	NEXT

	defcode	"=", w_equal			// ( a b -- flag )
	ldr	x0, [DSP], #8
	cmp	x0, TOS
	csetm	TOS, eq
	NEXT

	defcode	"<", w_less			// ( n1 n2 -- flag )
	ldr	x0, [DSP], #8
	cmp	x0, TOS
	csetm	TOS, lt
	NEXT

	defcode	"u<", w_uless			// ( u1 u2 -- flag )
	ldr	x0, [DSP], #8
	cmp	x0, TOS
	csetm	TOS, lo
	NEXT

	defcode	"0=", w_zequal			// ( x -- flag )
	cmp	TOS, #0
	csetm	TOS, eq
	NEXT

	defcode	"0<", w_zless			// ( n -- flag )
	asr	TOS, TOS, #63
	NEXT

// ---- Memory

	defcode	"@", w_fetch			// ( addr -- x )
	ldr	TOS, [TOS]
	NEXT

	defcode	"!", w_store			// ( x addr -- )
	ldr	x0, [DSP], #8
	str	x0, [TOS]
	ldr	TOS, [DSP], #8
	NEXT

	defcode	"c@", w_cfetch			// ( addr -- c )
	ldrb	TOSW, [TOS]
	NEXT

	defcode	"c!", w_cstore			// ( c addr -- )
	ldr	x0, [DSP], #8
	strb	w0, [TOS]
	ldr	TOS, [DSP], #8
	NEXT

// ---- Device access: sized loads and stores for device registers and DMA
// structures, and the barriers that order them. Drivers are Forth (hal/).

	defcode	"l@", w_lfetch			// ( addr -- u ) 32 bits, zero-extended
	ldr	TOSW, [TOS]
	NEXT

	defcode	"l!", w_lstore			// ( u addr -- ) low 32 bits
	ldr	x0, [DSP], #8
	str	w0, [TOS]
	ldr	TOS, [DSP], #8
	NEXT

	defcode	"w@", w_wfetch			// ( addr -- u ) 16 bits, zero-extended
	ldrh	TOSW, [TOS]
	NEXT

	defcode	"w!", w_wstore			// ( u addr -- ) low 16 bits
	ldr	x0, [DSP], #8
	strh	w0, [TOS]
	ldr	TOS, [DSP], #8
	NEXT

	defcode	"dmb", w_dmb			// ( -- ) earlier memory accesses complete before later ones
	dmb	sy
	NEXT

	defcode	"dsb", w_dsb			// ( -- ) ... and before any later instruction, e.g. a doorbell write
	dsb	sy
	NEXT

// ---- Tasks and time. PAUSE is the whole scheduler: cooperative round robin
// over the ring of user areas. tasks.fs builds the rest on it.

	defcode	"pause", w_pause		// ( -- ) let the next ready task run
	CHECK_STACKS				// a task must not be switched out broken
	ldp	x9, x10, [UP, #U_S0]
	cmp	DSP, x9
	b.hi	err_underflow
	cmp	RSP, x10
	b.hi	err_runderflow
	RPUSH	IP
	str	TOS, [DSP, #-8]!
	str	DSP, [UP, #U_SP]
	str	RSP, [UP, #U_RP]
	mov	x28, UP				// the search ends back at this task
1:	ldr	UP, [UP, #U_LINK]
	ldr	x0, [UP, #U_STATUS]
	cbz	x0, 3f				// ready
	ldr	x1, [UP, #U_WAKE]
	cbz	x1, 2f				// asleep until another task wakes it
	isb
	mrs	x2, cntvct_el0
	cmp	x2, x1
	b.lo	2f
	str	xzr, [UP, #U_STATUS]		// its time has come
	b	3f
2:	cmp	UP, x28
	b.ne	1b
	ldr	x1, =var_task_ticks		// nothing can run: wait for an interrupt.
	str	xzr, [x1]			// Idling is not running too long.
	bl	hal_idle
	b	1b
3:	ldr	x1, =var_task_ticks
	str	xzr, [x1]
	ldr	DSP, [UP, #U_SP]
	ldr	RSP, [UP, #U_RP]
	ldr	TOS, [DSP], #8
	RPOP	IP
	NEXT
pause_end:

	defcode	"up@", w_upfetch		// ( -- task ) this task: its user area
	PUSH	UP
	NEXT

	defcode	"counter", w_counter		// ( -- u ) the system counter
	isb
	mrs	x0, cntvct_el0
	PUSH	x0
	NEXT

	defcode	"counter-hz", w_counterhz	// ( -- u ) counter ticks per second
	mrs	x0, cntfrq_el0
	PUSH	x0
	NEXT

	defcode	"key?", w_keyq			// ( -- flag ) a key is waiting, or input has ended
	bl	hal_key_ready
	cmp	x0, #0
	csetm	x0, ne
	PUSH	x0
	NEXT

// ---- Platform words. The kernel is assembled once per platform (kernel.s).

.ifdef HOSTED
	defcode	"syscall", w_syscall		// ( a b c d n -- r ) Linux system call n
	mov	x8, TOS
	ldr	x3, [DSP], #8
	ldr	x2, [DSP], #8
	ldr	x1, [DSP], #8
	ldr	x0, [DSP], #8
	svc	#0
	mov	TOS, x0
	NEXT

	defcode	"args", w_args			// ( -- addr ) argc, then the argv pointers
	ldr	x0, =linux_args
	ldr	x0, [x0]
	PUSH	x0
	NEXT
.else
	defcode	">phys", w_tophys		// ( addr -- paddr ) the address a device must use for DMA
	VIRT_TO_PHYS TOS, x0
	NEXT
.endif

// ---- Counted loops. Loop parameters on the return stack: index on top, then limit.
// These are hot paths, so they are primitives; DO, LOOP and friends are in core.fs.

	defcode	"(do)", w_pdo, F_CONLY		// ( limit start -- ) ( R: -- limit start )
	ldr	x0, [DSP], #8
	RPUSH	x0
	RPUSH	TOS
	ldr	TOS, [DSP], #8
	NEXT

	// ( limit start -- ) skip the loop, to the address that follows, if limit = start
	defcode	"(?do)", w_pqdo, F_CONLY
	ldr	x0, [DSP], #8
	cmp	x0, TOS
	b.eq	1f
	RPUSH	x0
	RPUSH	TOS
	ldr	TOS, [DSP], #8
	add	IP, IP, #8
	NEXT
1:	ldr	TOS, [DSP], #8
	ldr	IP, [IP]
	NEXT

	defcode	"(loop)", w_ploop, F_CONLY	// ( -- ) step by 1; loop back to the address that follows
	CHECK_STACKS
	ldr	x0, [RSP]
	add	x0, x0, #1
	ldr	x1, [RSP, #8]
	cmp	x0, x1
	b.eq	1f
	str	x0, [RSP]
	ldr	IP, [IP]
	NEXT
1:	add	RSP, RSP, #16
	add	IP, IP, #8
	NEXT

	// ( n -- ) step by n. Ends when the index crosses the boundary between
	// limit-1 and limit, in either direction.
	defcode	"(+loop)", w_pplusloop, F_CONLY
	CHECK_STACKS
	ldr	x0, [RSP]
	ldr	x1, [RSP, #8]
	sub	x2, x0, x1			// old index - limit
	add	x3, x2, TOS			// new index - limit
	add	x0, x0, TOS
	eor	x4, x2, x3			// sign changed...
	eor	x5, x2, TOS			// ...and not by overflow
	and	x4, x4, x5
	ldr	TOS, [DSP], #8
	tbnz	x4, #63, 1f
	str	x0, [RSP]
	ldr	IP, [IP]
	NEXT
1:	add	RSP, RSP, #16
	add	IP, IP, #8
	NEXT

	defcode	"i", w_i, F_CONLY			// ( -- n ) innermost loop index
	str	TOS, [DSP, #-8]!
	ldr	TOS, [RSP]
	NEXT

	defcode	"j", w_j, F_CONLY			// ( -- n ) next outer loop index
	str	TOS, [DSP, #-8]!
	ldr	TOS, [RSP, #16]
	NEXT

	defcode	"unloop", w_unloop, F_CONLY		// ( -- ) ( R: limit index -- )
	add	RSP, RSP, #16
	NEXT

// ---- Terminal (through the HAL)

	defcode	"key", w_key			// ( -- c ) -1 at end of input
	bl	hal_key
	PUSH	x0
	NEXT

	defcode	"emit", w_emit			// ( c -- )
	POP	x0
	bl	hal_emit
	NEXT

	defcode	"bye", w_bye			// ( -- )
	mov	x0, #0
	b	hal_bye

// ---- A measured hot spot: SHA-256's block function (FIPS 180-4). In Forth
// a block took 27 ms under emulation, so a password hash took minutes.
// crypto.fs has COMPRESS-REF, the Forth definition, which tests/reference
// checks against this. The state is eight cells, each a 32-bit word; w is
// room for the 64-word message schedule (256 bytes); k is the 64 round
// constants, a cell each. Working variables a-h are w4-w11.

	defcode	"sha256-block", w_sha256block	// ( block state w k -- )
	POP	x3
	POP	x2
	POP	x1
	POP	x0
	mov	x12, #0				// the schedule: 16 big-endian words,
1:	ldr	w13, [x0, x12, lsl #2]
	rev	w13, w13
	str	w13, [x2, x12, lsl #2]
	add	x12, x12, #1
	cmp	x12, #16
	b.lo	1b
2:	sub	x13, x12, #2			// then W[i] = sigma1(W[i-2]) + W[i-7]
	ldr	w14, [x2, x13, lsl #2]		//   + sigma0(W[i-15]) + W[i-16]
	ror	w15, w14, #17
	eor	w15, w15, w14, ror #19
	eor	w15, w15, w14, lsr #10
	sub	x13, x12, #15
	ldr	w14, [x2, x13, lsl #2]
	ror	w24, w14, #7
	eor	w24, w24, w14, ror #18
	eor	w24, w24, w14, lsr #3
	add	w15, w15, w24
	sub	x13, x12, #16
	ldr	w14, [x2, x13, lsl #2]
	add	w15, w15, w14
	sub	x13, x12, #7
	ldr	w14, [x2, x13, lsl #2]
	add	w15, w15, w14
	str	w15, [x2, x12, lsl #2]
	add	x12, x12, #1
	cmp	x12, #64
	b.lo	2b
	ldp	x4, x5, [x1]
	ldp	x6, x7, [x1, #16]
	ldp	x8, x9, [x1, #32]
	ldp	x10, x11, [x1, #48]
	mov	x12, #0
3:	ror	w13, w8, #6			// t1 = h + Sigma1(e) + Ch(e,f,g) + K[i] + W[i]
	eor	w13, w13, w8, ror #11
	eor	w13, w13, w8, ror #25
	and	w14, w8, w9
	bic	w15, w10, w8
	eor	w14, w14, w15
	add	w13, w13, w14
	add	w13, w13, w11
	ldr	x14, [x3, x12, lsl #3]
	add	w13, w13, w14
	ldr	w14, [x2, x12, lsl #2]
	add	w13, w13, w14
	ror	w14, w4, #2			// t2 = Sigma0(a) + Maj(a,b,c)
	eor	w14, w14, w4, ror #13
	eor	w14, w14, w4, ror #22
	and	w15, w4, w5
	and	w24, w4, w6
	eor	w15, w15, w24
	and	w24, w5, w6
	eor	w15, w15, w24
	add	w14, w14, w15
	mov	w11, w10			// h = g, g = f, f = e, e = d + t1,
	mov	w10, w9				// d = c, c = b, b = a, a = t1 + t2
	mov	w9, w8
	add	w8, w7, w13
	mov	w7, w6
	mov	w6, w5
	mov	w5, w4
	add	w4, w13, w14
	add	x12, x12, #1
	cmp	x12, #64
	b.lo	3b
	ldp	x12, x13, [x1]			// add a-h into the state
	add	w12, w12, w4
	add	w13, w13, w5
	stp	x12, x13, [x1]
	ldp	x12, x13, [x1, #16]
	add	w12, w12, w6
	add	w13, w13, w7
	stp	x12, x13, [x1, #16]
	ldp	x12, x13, [x1, #32]
	add	w12, w12, w8
	add	w13, w13, w9
	stp	x12, x13, [x1, #32]
	ldp	x12, x13, [x1, #48]
	add	w12, w12, w10
	add	w13, w13, w11
	stp	x12, x13, [x1, #48]
	NEXT

// ---- Measured hot spots: memory copies and fills. In Forth they cost about
// 11 us a byte under emulation, so moving a block buffer took 11 ms. core.fs
// has CMOVE-REF, CMOVE>-REF and FILL-REF, which tests/reference checks.

	defcode	"cmove", w_cmove		// ( src dst u -- ) copy, lowest address first
	POP	x2
	POP	x1
	POP	x0
	cbz	x2, 2f
1:	ldrb	w12, [x0], #1
	strb	w12, [x1], #1
	subs	x2, x2, #1
	b.ne	1b
2:	NEXT

	defcode	"cmove>", w_cmoveup		// ( src dst u -- ) copy, highest address first
	POP	x2
	POP	x1
	POP	x0
	cbz	x2, 2f
1:	subs	x2, x2, #1
	ldrb	w12, [x0, x2]
	strb	w12, [x1, x2]
	b.ne	1b
2:	NEXT

	defcode	"fill", w_fill			// ( addr u c -- )
	POP	x2
	POP	x1
	POP	x0
	cbz	x1, 2f
1:	strb	w2, [x0], #1
	subs	x1, x1, #1
	b.ne	1b
2:	NEXT

// SHA-256's output: the state's eight 32-bit words, big-endian, at addr.
	defcode	"sha256-out", w_sha256out	// ( state addr -- )
	POP	x1
	POP	x0
	mov	x12, #0
1:	ldr	x13, [x0, x12, lsl #3]
	rev	w13, w13
	str	w13, [x1, x12, lsl #2]
	add	x12, x12, #1
	cmp	x12, #8
	b.lo	1b
	NEXT
