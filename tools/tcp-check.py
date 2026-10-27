#!/usr/bin/env python3
"""The client side of `make tcp-check`: real sockets, so the host's own TCP
stack talks to the OS through QEMU's user networking, which forwards ports 4000
and 4001. Eight sandbox sessions at once on 4000 each send fifty lines of
arithmetic and check every answer; one full-Forth session on 4001 defines and
runs a word. Each session ends with bye, and the OS must close it. Prints a
summary; run by console-run.py as a peer.
"""

import socket
import threading
import time

CLIENTS, LINES = 8, 50


def open_session(port, password=None):
    """Connect, log in if a password is given, and read the greeting; None if
    the OS does not answer."""
    for _ in range(20):                         # the OS may still be starting
        try:
            s = socket.create_connection(("127.0.0.1", port), timeout=10)
            got = b""
            while b"leave.\r\n" not in got:
                chunk = s.recv(4096)
                if not chunk:
                    break
                got += chunk
                if password and got.endswith(b"Password: "):
                    s.sendall(password + b"\r\n")
            if b"leave.\r\n" in got:
                return s
            s.close()
        except OSError:
            pass
        time.sleep(1)
    return None


def read_until(s, count, marker=b"ok\r\n"):
    got = b""
    while got.count(marker) < count:
        chunk = s.recv(65536)
        if not chunk:
            break
        got += chunk
    return got


def closed_by_os(s):
    try:
        while s.recv(4096):
            pass
        return True
    except OSError:
        return False
    finally:
        s.close()


def sandbox_client(n, results):
    s = open_session(4000)
    if s is None:
        results[n] = "could not connect"
        return
    s.sendall(b"".join(f"{j} {n + 2} * .\r\n".encode() for j in range(LINES)))
    got = read_until(s, LINES)
    wrong = [j for j in range(LINES) if f" * . {j * (n + 2)}  ok\r\n".encode() not in got]
    s.sendall(b"bye\r\n")
    closed = closed_by_os(s)
    results[n] = "ok" if not wrong and closed else f"wrong answers {wrong[:3]}" if wrong else "not closed"


def admin_client():
    s = open_session(4001, b"secret")           # tcp-check.in sets it
    if s is None:
        return "could not connect"
    s.sendall(b": cube dup dup * * ;\r\n5 cube .\r\nbye\r\n")
    got = read_until(s, 3)
    closed = closed_by_os(s)
    return "ok" if b"125  ok" in got and closed else repr(got[-80:])


def main():
    time.sleep(2)
    t0 = time.time()
    results = {}
    threads = [threading.Thread(target=sandbox_client, args=(n, results)) for n in range(CLIENTS)]
    for t in threads:
        t.start()
    for t in threads:
        t.join(60)
    ok = sum(r == "ok" for r in results.values())
    print(f"tcp-check: {ok} of {CLIENTS} sandbox sessions answered {LINES} lines and closed", flush=True)
    for n, r in sorted(results.items()):
        if r != "ok":
            print(f"tcp-check: session {n}: {r}", flush=True)
    print(f"tcp-check: full-Forth session: {admin_client()}", flush=True)
    print(f"tcp-check: took {time.time() - t0:.1f}s", flush=True)


if __name__ == "__main__":
    main()
