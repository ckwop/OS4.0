#!/usr/bin/env python3
"""Host-side tool for OS 4.0 data disks: raw images of 1 KiB blocks.

Block 0 is the header, matching forth/blocks.fs: the magic "OS40DISK", then
three little-endian 64-bit cells: format version, volume ID and size in blocks.
Source is stored as screens of 16 lines of 64 characters, with no newlines.

  blocks.py format IMAGE [--blocks N] [--volume-id ID] [--force]
  blocks.py info IMAGE
  blocks.py list IMAGE FIRST [LAST]     print screens as text
  blocks.py put IMAGE FIRST FILE        store a text file as screens from FIRST
"""

import argparse
import os
import secrets
import struct
import sys

BLOCK = 1024
LINE = 64
LINES = 16
MAGIC = b"OS40DISK"
VERSION = 1
HEADER = struct.Struct("<8sQQQ")


def read_header(f):
    f.seek(0)
    raw = f.read(HEADER.size)
    if len(raw) < HEADER.size:
        return None
    magic, version, volume, blocks = HEADER.unpack(raw)
    if magic != MAGIC or version != VERSION:
        return None
    return volume, blocks


def cmd_format(args):
    if os.path.exists(args.image) and not args.force:
        with open(args.image, "rb") as f:
            if read_header(f):
                sys.exit(f"{args.image} is already a data disk; use --force to replace it")
    volume = args.volume_id if args.volume_id is not None else secrets.randbits(63)
    with open(args.image, "wb") as f:
        f.truncate(args.blocks * BLOCK)             # sparse where the filesystem allows
        f.write(HEADER.pack(MAGIC, VERSION, volume, args.blocks))
    print(f"{args.image}: volume {volume}, {args.blocks} blocks")


def open_disk(path, mode="rb"):
    f = open(path, mode)
    header = read_header(f)
    if not header:
        sys.exit(f"{path} has no valid data disk header")
    return f, header


def cmd_info(args):
    f, (volume, blocks) = open_disk(args.image)
    print(f"volume {volume}, {blocks} blocks, format version {VERSION}")


def screen_lines(data):
    for i in range(LINES):
        text = data[i * LINE:(i + 1) * LINE]
        yield "".join(chr(c) if 32 <= c < 127 else " " for c in text).rstrip()


def cmd_list(args):
    f, (_, blocks) = open_disk(args.image)
    last = args.last if args.last is not None else args.first
    for n in range(args.first, last + 1):
        if not 0 <= n < blocks:
            sys.exit(f"block {n} is outside the disk")
        f.seek(n * BLOCK)
        print(f"Screen {n}")
        for i, line in enumerate(screen_lines(f.read(BLOCK).ljust(BLOCK, b"\0"))):
            print(f"{i:2} {line}")


def cmd_put(args):
    with open(args.file, encoding="ascii") as src:
        lines = src.read().splitlines()
    for i, line in enumerate(lines, 1):
        if len(line) > LINE:
            sys.exit(f"{args.file}:{i}: longer than {LINE} characters")
    screens = [lines[i:i + LINES] for i in range(0, max(len(lines), 1), LINES)]
    f, (_, blocks) = open_disk(args.image, "r+b")
    if args.first < 1 or args.first + len(screens) > blocks:
        sys.exit("screens must fit between block 1 and the end of the disk")
    for n, screen in enumerate(screens, args.first):
        text = "".join(line.ljust(LINE) for line in screen).ljust(BLOCK)
        f.seek(n * BLOCK)
        f.write(text.encode("ascii"))
    print(f"{args.file}: {len(screens)} screen(s) from block {args.first}")


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="command", required=True)
    s = sub.add_parser("format")
    s.add_argument("image")
    s.add_argument("--blocks", type=int, default=4096)
    s.add_argument("--volume-id", type=int)
    s.add_argument("--force", action="store_true")
    s.set_defaults(run=cmd_format)
    s = sub.add_parser("info")
    s.add_argument("image")
    s.set_defaults(run=cmd_info)
    s = sub.add_parser("list")
    s.add_argument("image")
    s.add_argument("first", type=int)
    s.add_argument("last", type=int, nargs="?")
    s.set_defaults(run=cmd_list)
    s = sub.add_parser("put")
    s.add_argument("image")
    s.add_argument("first", type=int)
    s.add_argument("file")
    s.set_defaults(run=cmd_put)
    args = p.parse_args()
    args.run(args)


if __name__ == "__main__":
    main()
