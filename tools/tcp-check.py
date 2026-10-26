#!/usr/bin/env python3
"""The TCP client side of `make tcp-check`: real sockets, so the host's own TCP
stack talks to the OS through QEMU's user networking, which forwards port 4000.
Several clients at once each send lines to the OS's echo server and check the
echoes, then close. Prints one summary line; run by console-run.py as a peer.
"""

import socket
import threading
import time

CLIENTS, LINES = 8, 50


def client(n, results):
    for _ in range(20):                         # the server may not be up yet
        try:
            s = socket.create_connection(("127.0.0.1", 4000), timeout=10)
            s.sendall(b"hello\r\n")
            reply = b""
            while not reply.endswith(b"\n"):
                chunk = s.recv(64)
                if not chunk:
                    break
                reply += chunk
            if reply == b"hello\r\n":
                break
            s.close()
        except OSError:
            pass
        time.sleep(1)
    else:
        results[n] = "could not connect"
        return
    lines = [f"client {n} line {j} ".encode() + b"y" * (j * 4) for j in range(LINES)]
    s.sendall(b"".join(line + b"\r\n" for line in lines))     # all at once: many segments
    expected = b"".join(line + b"\r\n" for line in lines)
    got = b""
    while len(got) < len(expected):
        chunk = s.recv(65536)
        if not chunk:
            break
        got += chunk
    s.shutdown(socket.SHUT_WR)
    rest = s.recv(64)                           # the server closes after our FIN
    s.close()
    results[n] = "ok" if got == expected and rest == b"" else "wrong echo"


def main():
    time.sleep(2)
    results = {}
    t0 = time.time()
    threads = [threading.Thread(target=client, args=(n, results)) for n in range(CLIENTS)]
    for t in threads:
        t.start()
    for t in threads:
        t.join(60)
    ok = sum(r == "ok" for r in results.values())
    print(f"tcp-check: took {time.time() - t0:.1f}s", flush=True)
    print(f"tcp-check: {ok} of {CLIENTS} clients echoed {LINES} lines and closed", flush=True)
    for n, r in sorted(results.items()):
        if r != "ok":
            print(f"tcp-check: client {n}: {r}", flush=True)


if __name__ == "__main__":
    main()
