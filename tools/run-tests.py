#!/usr/bin/env python3
"""Run transcript tests, several at a time.

Each <dir>/<name>.in is fed to a Forth system on stdin, and the output is
compared with <dir>/<name>.out. If <dir>/<name>.filter exists, it is a sed
script applied to the output first, to mask values that change from build to
build (such as code addresses). The output is kept in <dir>/<name>.actual.

Every test gets its own data disk and network ports, so tests can run side by
side. In the command and in --setup, "{disk}" is replaced by the test's disk
image, "{port}" by the OS's UDP port for network frames and "{peerport}" by the
network peer's. If <dir>/<name>.peer exists, it holds the peer's command (with
the same placeholders), passed to tools/console-run.py as OS4_PEER.

Usage: run-tests.py --cmd "COMMAND {disk}" [--setup "COMMAND {disk}"]
                    [--jobs N] [--timeout SECONDS] [--disks DIR] DIR ...
"""

import argparse
import concurrent.futures
import difflib
import os
import shlex
import subprocess
import sys


def run_test(index, path, args):
    name = os.path.splitext(path)[0]
    port = args.base_port + 2 * index
    fill = dict(disk=os.path.join(args.disks, name.replace(os.sep, "-") + ".img"),
                port=port, peerport=port + 1)
    if args.setup:
        setup = subprocess.run(shlex.split(args.setup.format(**fill)), capture_output=True)
        if setup.returncode:
            return name, False, f"setup failed:\n{setup.stdout.decode()}{setup.stderr.decode()}"
    env = dict(os.environ)
    env.pop("OS4_PEER", None)
    if os.path.exists(name + ".peer"):
        with open(name + ".peer") as f:
            env["OS4_PEER"] = f.read().strip().format(**fill)

    with open(path, "rb") as stdin:
        proc = subprocess.Popen(shlex.split(args.cmd.format(**fill)), stdin=stdin, env=env,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        try:
            output = proc.communicate(timeout=args.timeout)[0]
        except subprocess.TimeoutExpired:
            proc.terminate()                    # console-run then shows how far it got
            try:
                output = proc.communicate(timeout=10)[0]
            except subprocess.TimeoutExpired:
                proc.kill()
                output = proc.communicate()[0]
            output += f"[timed out after {args.timeout} s]\n".encode()
    if os.path.exists(name + ".filter"):
        output = subprocess.run(["sed", "-f", name + ".filter"], input=output,
                                stdout=subprocess.PIPE, check=True).stdout
    with open(name + ".actual", "wb") as f:
        f.write(output)

    try:
        with open(name + ".out", "rb") as f:
            expected = f.read()
    except FileNotFoundError:
        return name, False, f"{name}.out is missing"
    if output == expected:
        return name, True, ""
    diff = difflib.unified_diff(expected.decode(errors="replace").splitlines(True),
                                output.decode(errors="replace").splitlines(True),
                                name + ".out", name + ".actual")
    return name, False, "".join(diff)


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--cmd", required=True)
    p.add_argument("--setup")
    p.add_argument("--jobs", type=int, default=os.cpu_count() or 1)
    p.add_argument("--timeout", type=float, default=30)
    p.add_argument("--disks", default="build/test-disks")
    p.add_argument("--base-port", type=int, default=21000)
    p.add_argument("dirs", nargs="+")
    args = p.parse_args()

    os.makedirs(args.disks, exist_ok=True)
    tests = sorted(os.path.join(d, f) for d in args.dirs
                   for f in os.listdir(d) if f.endswith(".in"))
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        results = list(pool.map(lambda it: run_test(*it, args), enumerate(tests)))

    failed = 0
    for name, ok, report in results:
        if not ok:
            failed += 1
            print(report, end="" if report.endswith("\n") else "\n")
            print(f"FAIL: {name}")
    print(f"{len(results) - failed} passed, {failed} failed")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
