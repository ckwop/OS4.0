/* virt.ld: link the bare-metal kernel for Limine, which requires the higher half.
   One RWX segment: the dictionary holds code fields written at run time, and the
   brief's memory model is a single flat address space. */

OUTPUT_FORMAT(elf64-littleaarch64)
ENTRY(_start)

PHDRS
{
    image PT_LOAD FLAGS(7);
}

SECTIONS
{
    . = 0xffffffff80000000;

    .text : { *(.text .text.*) } :image
    .rodata : { *(.rodata .rodata.*) } :image
    .data : {
        *(.data .data.*)
        KEEP(*(.limine_requests))
    } :image
    .bss : { *(.bss .bss.*) *(COMMON) } :image

    /DISCARD/ : { *(.note .note.*) *(.comment) *(.eh_frame*) }
}
