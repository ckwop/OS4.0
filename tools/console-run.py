#!/usr/bin/env python3
"""Run the OS as if it were a program reading stdin, rebooting where asked.

Reads Forth input on stdin and runs the command given as arguments (QEMU for
bare metal, or the hosted binary). Once the banner appears, it types the input,
then Ctrl-D, which makes the Forth power off or exit. Input is held back until
the banner so firmware cannot swallow it during boot.

A line consisting of REBOOT_MARKER splits the input: after each part the
system shuts down and the command runs again, on the same disks.

Writes the console output from each banner onwards to stdout with CRs removed,
so transcripts are the same for every platform.

Usage: console-run.py command [args ...]
"""

import os
import subprocess
import sys
import threading

BANNER = b"OS 4.0\n"
CTRL_D = b"\x04"
REBOOT_MARKER = b"\\ --- reboot ---"


def run_once(command, data):
    """Boot, type data, shut down. Returns (exit status, console output)."""
    if data and not data.endswith(b"\n"):
        data += b"\n"
    proc = subprocess.Popen(command, stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    def type_input():
        proc.stdin.write(data + CTRL_D)
        proc.stdin.flush()

    output = bytearray()
    typing = None
    while True:
        chunk = os.read(proc.stdout.fileno(), 4096)
        if not chunk:
            break
        output += chunk.replace(b"\r", b"")
        if typing is None and BANNER in output:
            typing = threading.Thread(target=type_input, daemon=True)
            typing.start()
    status = proc.wait()

    start = output.find(BANNER)
    if start < 0:
        return 1, b"console-run: no banner; console output was:\n" + output
    return status, output[start:]


def main():
    parts = [[]]
    for line in sys.stdin.buffer.read().splitlines(keepends=True):
        if line.rstrip(b"\r\n") == REBOOT_MARKER:
            parts.append([])
        else:
            parts[-1].append(line)

    for part in parts:
        status, output = run_once(sys.argv[1:], b"".join(part))
        sys.stdout.buffer.write(output)
        sys.stdout.buffer.flush()
        if status:
            return status
    return 0


if __name__ == "__main__":
    sys.exit(main())
