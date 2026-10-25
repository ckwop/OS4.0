// prims.s: primitive words: inner interpreter, stack, arithmetic, memory,
// counted loops and the terminal. Included by kernel.s.

	.text

// ---- Inner interpreter

	defcode	"exit", w_exit			// ( -- ) ( R: ip -- )
	RPOP	IP
	NEXT

	defcode	"lit", w_lit			// ( -- x ) push the cell that follows
	str	TOS, [DSP, #-8]!
	ldr	TOS, [IP], #8
	NEXT

	defcode	"branch", w_branch		// ( -- ) jump to the address that follows
	ldr	IP, [IP]
	NEXT

	defcode	"0branch", w_zbranch		// ( flag -- ) jump if flag is zero
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

	defcode	">r", w_tor			// ( x -- ) ( R: -- x )
	RPUSH	TOS
	ldr	TOS, [DSP], #8
	NEXT

	defcode	"r>", w_rfrom			// ( -- x ) ( R: x -- )
	str	TOS, [DSP, #-8]!
	RPOP	TOS
	NEXT

	defcode	"r@", w_rfetch			// ( -- x ) ( R: x -- x )
	str	TOS, [DSP, #-8]!
	ldr	TOS, [RSP]
	NEXT

	defcode	"depth", w_depth		// ( -- n )
	ldr	x0, =dstack_top
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

	defcode	"sp!", w_spstore		// ( addr -- i*x ) the stack as it was at SP@
	add	DSP, TOS, #8
	ldr	TOS, [TOS]
	NEXT

	defcode	"rp@", w_rpfetch		// ( -- addr )
	PUSH	RSP
	NEXT

	defcode	"rp!", w_rpstore		// ( addr -- ) ( R: i*x -- j*x )
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

// ---- Counted loops. Loop parameters on the return stack: index on top, then limit.
// These are hot paths, so they are primitives; DO, LOOP and friends are in core.fs.

	defcode	"(do)", w_pdo			// ( limit start -- ) ( R: -- limit start )
	ldr	x0, [DSP], #8
	RPUSH	x0
	RPUSH	TOS
	ldr	TOS, [DSP], #8
	NEXT

	// ( limit start -- ) skip the loop, to the address that follows, if limit = start
	defcode	"(?do)", w_pqdo
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

	defcode	"(loop)", w_ploop		// ( -- ) step by 1; loop back to the address that follows
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
	defcode	"(+loop)", w_pplusloop
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

	defcode	"i", w_i			// ( -- n ) innermost loop index
	str	TOS, [DSP, #-8]!
	ldr	TOS, [RSP]
	NEXT

	defcode	"j", w_j			// ( -- n ) next outer loop index
	str	TOS, [DSP, #-8]!
	ldr	TOS, [RSP, #16]
	NEXT

	defcode	"unloop", w_unloop		// ( -- ) ( R: limit index -- )
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
