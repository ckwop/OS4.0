// virt.s: platform glue for bare metal on QEMU's "virt" machine, booted by
// Limine (milestone 3). Replaces linux.s; the kernel is unchanged.
//
// Limine enters _start at EL1 with the MMU on, the kernel mapped in the higher
// half and a 64 KiB stack. It does not map devices, so we map the low 1 GiB,
// where virt keeps its MMIO, as Device memory through TTBR0, which the protocol
// leaves to us.
//
// HAL contract, as for linux.s (AAPCS64; may clobber x0-x15, x30):
//   hal_key   -> x0 next input character (waits)
//   hal_emit  x0 character ->
//   hal_bye   x0 exit status -> powers off; does not return

	.include "macros.s"

	.equ	UART_BASE, 0x09000000		// PL011
	.equ	UART_DR, 0x00
	.equ	UART_FR, 0x18
	.equ	UART_CR, 0x30
	.equ	FR_RXFE, 4			// bit: receive FIFO empty
	.equ	FR_TXFF, 5			// bit: transmit FIFO full
	.equ	CR_ENABLE, 0x301		// UARTEN | TXE | RXE

	.equ	PSCI_SYSTEM_OFF, 0x84000008

	.equ	MAIR_DEVICE_NGNRE, 0x04
	.equ	MAIR_IDX_DEVICE, 2		// Limine uses attribute slots 0 and 1
	.equ	TCR_EPD0, 1 << 7		// disables TTBR0 walks when set
	.equ	PTE_TABLE, 0x3
	// 1 GiB block at physical 0: Device memory, access flag set, never executable
	.equ	PTE_DEVICE_BLOCK, (1 << 54) | (1 << 53) | (1 << 10) | (MAIR_IDX_DEVICE << 2) | 0x1

	.equ	CH_LF, 10
	.equ	CH_CR, 13

// ---------------------------------------------------------------------------
// Limine requests: just the base revision for now. Limine 9.6 supports up to 3.

	.section .limine_requests, "aw"
	.balign	8
	.quad	0xf6b8f4b39de7d1ae, 0xfab91a6940fcb9cf, 0x785c6ed015d3e316, 0x181e920a7852b9d9
limine_base_revision:
	.quad	0xf9562b2d5c95a6c8, 0x6a7b384944536bdc, 3
	.quad	0xadc0e0531bb10d03, 0x9572709f31764c62

	.section .rodata
msg_revision:
	.ascii	"Limine did not accept base revision 3\n"
	.equ	msg_revision_len, . - msg_revision

// ---------------------------------------------------------------------------

	.text
	.global	_start
_start:
	ldr	x0, =vectors
	msr	vbar_el1, x0
	isb
	bl	map_devices
	bl	uart_init
	ldr	x0, =limine_base_revision	// Limine zeroes the last cell if it complied
	ldr	x0, [x0, #16]
	cbz	x0, 1f
	ldr	x0, =msg_revision
	mov	x1, #msg_revision_len
	bl	type_sub
	mov	x0, #1
	b	hal_bye
1:	b	forth_cold

// Map virtual 0 - 1 GiB to physical 0 - 1 GiB as Device-nGnRE, through TTBR0.
map_devices:
	ldr	x0, =mmio_l0			// level 0 entry 0 -> the level 1 table
	VIRT_TO_PHYS x0, x1
	mov	x9, x0
	ldr	x0, =mmio_l1
	VIRT_TO_PHYS x0, x1
	orr	x0, x0, #PTE_TABLE
	ldr	x1, =mmio_l0
	str	x0, [x1]
	ldr	x0, =PTE_DEVICE_BLOCK		// level 1 entry 0 -> the 1 GiB block
	ldr	x1, =mmio_l1
	str	x0, [x1]
	dsb	ish
	mrs	x0, mair_el1
	bic	x0, x0, #(0xff << (8 * MAIR_IDX_DEVICE))
	orr	x0, x0, #(MAIR_DEVICE_NGNRE << (8 * MAIR_IDX_DEVICE))
	msr	mair_el1, x0
	mrs	x0, tcr_el1
	bic	x0, x0, #TCR_EPD0
	msr	tcr_el1, x0
	msr	ttbr0_el1, x9
	isb
	tlbi	vmalle1
	dsb	ish
	isb
	ret

// The firmware has set the PL011 up; make sure it is enabled.
uart_init:
	ldr	x0, =UART_BASE
	mov	w1, #CR_ENABLE
	str	w1, [x0, #UART_CR]
	ret

	.global	hal_key
hal_key:
	ldr	x1, =UART_BASE
1:	ldr	w2, [x1, #UART_FR]
	tbnz	w2, #FR_RXFE, 1b
	ldr	w0, [x1, #UART_DR]
	and	w0, w0, #0xff
	ret

	.global	hal_emit
hal_emit:				// a terminal needs CR before LF
	ldr	x1, =UART_BASE
	cmp	w0, #CH_LF
	b.ne	2f
	mov	w3, #CH_CR
1:	ldr	w2, [x1, #UART_FR]
	tbnz	w2, #FR_TXFF, 1b
	str	w3, [x1, #UART_DR]
2:	ldr	w2, [x1, #UART_FR]
	tbnz	w2, #FR_TXFF, 2b
	str	w0, [x1, #UART_DR]
	ret

	.global	hal_bye
hal_bye:
	ldr	x0, =PSCI_SYSTEM_OFF
	hvc	#0
1:	wfi					// PSCI failed: stop here
	b	1b

	.bss
	.balign	4096
mmio_l0:	.space	4096
mmio_l1:	.space	4096
