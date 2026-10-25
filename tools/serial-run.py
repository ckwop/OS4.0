#!/usr/bin/env python3
"""Run the bare-metal kernel under QEMU as if it were a program reading stdin.

Reads Forth input on stdin and starts the QEMU command given as arguments. Once
the banner appears on the serial console, it types the input followed by Ctrl-D,
which makes the Forth power the machine off. Input is held back until then so the
firmware cannot swallow it during boot.

Writes the console output from the banner onwards to stdout with CRs removed, so
transcripts match the hosted build's.

Usage: serial-run.py qemu-system-aarch64 ...
"""

import os
import subprocess
import sys
import threading

BANNER = b"OS 4.0\n"
CTRL_D = b"\x04"


def main():
    data = sys.stdin.buffer.read()
    if data and not data.endswith(b"\n"):
        data += b"\n"
    qemu = subprocess.Popen(sys.argv[1:], stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    def type_input():
        qemu.stdin.write(data + CTRL_D)
        qemu.stdin.flush()

    output = bytearray()
    typing = None
    while True:
        chunk = os.read(qemu.stdout.fileno(), 4096)
        if not chunk:
            break
        output += chunk.replace(b"\r", b"")
        if typing is None and BANNER in output:
            typing = threading.Thread(target=type_input, daemon=True)
            typing.start()
    status = qemu.wait()

    start = output.find(BANNER)
    if start < 0:
        sys.stdout.buffer.write(b"serial-run: no banner; console output was:\n" + output)
        return 1
    sys.stdout.buffer.write(output[start:])
    return status


if __name__ == "__main__":
    sys.exit(main())
