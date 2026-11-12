#!/usr/bin/env python3
"""Break a FAT16 app disk on purpose, for tests of forth/files.fs against
hostile disks. tools/app-disk.sh runs it when the app directory holds a file
named .corrupt, after the files are copied in. Each line of that file is one
change (blank lines and lines starting with # are skipped); NAME is a file in
the root directory, by its 8.3 name, such as HELLO.TXT:

  chain NAME N        end the file's cluster chain after N clusters
  loop NAME K         point the file's K-th cluster (from 0) back at its first
  link NAME K V       set the FAT entry of the file's K-th cluster (from 0) to V
  start NAME C        set the file's first cluster to C
  size NAME S         set the file's size to S
  attr NAME A         set the file's attribute byte to A
  bpb OFFSET LEN V    store V, little-endian, in LEN bytes of the boot sector

Usage: fat-corrupt.py IMAGE CHANGES
"""
import struct
import sys


def main():
    img, changes = sys.argv[1], sys.argv[2]
    with open(img, "r+b") as f:
        disk = bytearray(f.read())
    bps, spc = struct.unpack_from("<HB", disk, 11)
    reserved, nfats, nroot = struct.unpack_from("<HBH", disk, 14)
    fatsz = struct.unpack_from("<H", disk, 22)[0]
    if fatsz == 0:
        sys.exit("fat-corrupt.py: FAT16 only")
    fat = reserved * bps
    root = fat + nfats * fatsz * bps

    def entry(name):
        base, _, ext = name.upper().partition(".")
        want = base.ljust(8).encode() + ext.ljust(3).encode()
        for i in range(nroot):
            off = root + 32 * i
            if disk[off + 11] != 0x0F and disk[off:off + 11] == want:
                return off
        sys.exit("fat-corrupt.py: no " + name)

    def link(c, v=None):  # every copy of the FAT
        if v is None:
            return struct.unpack_from("<H", disk, fat + 2 * c)[0]
        for k in range(nfats):
            struct.pack_into("<H", disk, fat + k * fatsz * bps + 2 * c, v)

    def chain(off):
        c, cs = struct.unpack_from("<H", disk, off + 26)[0], []
        while 2 <= c < 0xFFF8 and c not in cs:
            cs.append(c)
            c = link(c)
        return cs

    for line in open(changes):
        w = line.split()
        if not w or w[0].startswith("#"):
            continue
        op, args = w[0], w[1:]
        if op == "bpb":
            off, n, v = (int(a, 0) for a in args)
            disk[off:off + n] = v.to_bytes(n, "little")
            continue
        e = entry(args[0])
        if op == "chain":
            link(chain(e)[int(args[1]) - 1], 0xFFFF)
        elif op == "loop":
            cs = chain(e)
            link(cs[int(args[1], 0)], cs[0])
        elif op == "link":
            link(chain(e)[int(args[1], 0)], int(args[2], 0))
        elif op == "start":
            struct.pack_into("<H", disk, e + 26, int(args[1], 0))
        elif op == "size":
            struct.pack_into("<I", disk, e + 28, int(args[1], 0))
        elif op == "attr":
            disk[e + 11] = int(args[1], 0)
        else:
            sys.exit("fat-corrupt.py: unknown change " + op)
    with open(img, "r+b") as f:
        f.write(disk)


main()
