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

If OS4_PEER is set, it is a command (a network peer, tools/netpeer.py) started
once the first banner appears and stopped when the OS has shut down; what it
printed is added to the end of the transcript.

Usage: console-run.py command [args ...]
"""

import os
import shlex
import signal
import subprocess
import sys
import threading

BANNER = b"OS 4.0\n"
CTRL_D = b"\x04"
REBOOT_MARKER = b"\\ --- reboot ---"
current = []                    # the running system and its output so far
peers = []                      # the network peer, if one is running


def terminated(signum, frame):
    """Told to stop (a test that timed out): show how far the console got."""
    if current:
        proc, output = current
        proc.kill()
        start = max(output.find(BANNER), 0)
        sys.stdout.buffer.write(bytes(output[start:]) + b"\n[terminated]\n")
        sys.stdout.buffer.flush()
    for peer in peers:
        peer.kill()
    os._exit(1)


def run_once(command, data, on_banner=None):
    """Boot, type data, shut down. Returns (exit status, console output)."""
    if data and not data.endswith(b"\n"):
        data += b"\n"
    proc = subprocess.Popen(command, stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    def type_input():
        proc.stdin.write(data + CTRL_D)
        proc.stdin.flush()

    output = bytearray()
    current[:] = [proc, output]
    typing = None
    while True:
        chunk = os.read(proc.stdout.fileno(), 4096)
        if not chunk:
            break
        output += chunk.replace(b"\r", b"")
        if typing is None and BANNER in output:
            if on_banner:
                on_banner()
            typing = threading.Thread(target=type_input, daemon=True)
            typing.start()
    status = proc.wait()

    start = output.find(BANNER)
    if start < 0:
        return 1, b"console-run: no banner; console output was:\n" + output
    return status, output[start:]


def main():
    signal.signal(signal.SIGTERM, terminated)
    parts = [[]]
    for line in sys.stdin.buffer.read().splitlines(keepends=True):
        if line.rstrip(b"\r\n") == REBOOT_MARKER:
            parts.append([])
        else:
            parts[-1].append(line)

    peer = None

    def start_peer():
        nonlocal peer
        if peer is None and os.environ.get("OS4_PEER"):
            peer = subprocess.Popen(shlex.split(os.environ["OS4_PEER"]),
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            peers.append(peer)

    status = 0
    for part in parts:
        status, output = run_once(sys.argv[1:], b"".join(part), start_peer)
        sys.stdout.buffer.write(output)
        sys.stdout.buffer.flush()
        if status:
            break
    if peer:
        peer.terminate()
        sys.stdout.buffer.write(b"--- peer ---\n" + peer.communicate()[0])
    return status


if __name__ == "__main__":
    sys.exit(main())
