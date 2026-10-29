#!/usr/bin/env python3
"""Generate Lean definitions of Forth words from the dictionary as compiled.

Reads the dump that tools/dump-words.fs prints (make proofs-extract) and
writes a Lean module defining every word the model in proofs/OS4/Machine.lean
can express, over its primitives. Proofs are about these definitions, so
changing a word's Forth changes what is proven. A word is left out if it, or
anything it calls, needs something the model lacks; the report says what.

Words are named as in Forth. A name defined more than once gets #2, #3 ... on
its later definitions, oldest first ("allot#2"). The DOES> code of a defining
word W is "does:W".

Fails, rather than skipping, on a dump it cannot read. With --require FILE,
fails unless each word named in FILE was modelled.

Usage: forth2lean.py words.txt Words.lean [--require roots.txt]
"""

import re
import sys
from collections import Counter

# Primitives the model defines, by Forth name.
PRIMS = {
    "dup": "Prim.dup", "drop": "Prim.drop", "swap": "Prim.swap", "over": "Prim.over",
    ">r": "Prim.tor", "r>": "Prim.rfrom", "r@": "Prim.rfetch", "pick": "Prim.pick",
    "depth": "Prim.depth",
    "+": "Prim.plus", "-": "Prim.minus", "*": "Prim.star", "/mod": "Prim.slashmod",
    "um*": "Prim.umstar", "um/mod": "Prim.umslashmod",
    "and": "Prim.and", "or": "Prim.or", "xor": "Prim.xor", "invert": "Prim.invert",
    "lshift": "Prim.lshift", "rshift": "Prim.rshift",
    "=": "Prim.equal", "<": "Prim.less", "u<": "Prim.uless",
    "0=": "Prim.zequal", "0<": "Prim.zless",
    "@": "Prim.fetch", "!": "Prim.store", "c@": "Prim.cfetch", "c!": "Prim.cstore",
    "w@": "Prim.wfetch", "w!": "Prim.wstore", "l@": "Prim.lfetch", "l!": "Prim.lstore",
    "cmove": "Prim.cmove", "cmove>": "Prim.cmoveUp", "fill": "Prim.fill",
    "up@": "Prim.upfetch", "(do)": "Prim.pdo", "i": "Prim.i", "j": "Prim.j", "unloop": "Prim.unloop",
    # The outside world.
    "pause": "Prim.pause", "counter": "Prim.ask", "key": "Prim.ask", "key?": "Prim.ask",
    "emit": "Prim.emit", "syscall": "Prim.syscall", "bye": "Prim.bye",
    "dmb": "Prim.barrier", "dsb": "Prim.barrier", "execute": "executeM",
    "sha256-block": "Prim.sha256block", "sha256-out": "Prim.sha256out",
}
# Kernel words that only push an address or value (defconst, defuser, deftramp).
KCONST = {
    "'tib", "#tib", ">in", "state", "base", "watchdog-limit", "f-length", "f-compile-only",
    "f-hidden", "f-immediate", "user-free", "/user", "main-task", "dict-owner", "'dict-end",
    "dict-end", "task-rlimit", "task-slimit", "task-name", "task-r0", "task-s0", "task-rp",
    "task-sp", "task-wake", "task-status", "task-link", "blk", "handler", "errname", "'throw",
    "'quit", "latest", "dp", "docon", "dovar", "docol", "counter-hz", "args",
}
# Forth words replaced by a trusted specification in Machine.lean.
OVERRIDES = {"throw": "throwM", "catch": "catchM"}
# Thread cells followed by an operand.
BRANCHES = {"branch": "branch", "0branch": "zbranch", "(?do)": "qdo", "(loop)": "loop", "(+loop)": "ploop"}
KINDS = {0: "primitive", 1: "colon", 2: "constant", 3: "variable", 4: "does"}


class Word:
    def __init__(self, xt, kind, name, cells):
        self.xt, self.kind, self.name, self.cells = xt, kind, name, cells
        self.id = name


class Blocked(Exception):
    """The model cannot express a word: why, at the root of the trouble."""


def load(path):
    """The dump, oldest word first, with unique ids."""
    words, complete = [], False
    for line in open(path):
        f = line.split()
        if f == ["@@", "end"]:
            complete = True
        elif len(f) >= 4 and f[0] == "@@":
            if f[2] not in ("0", "1", "2", "3", "4"):
                sys.exit(f"{path}: {f[3]}: bad kind {f[2]}: is the dump garbled?")
            words.append(Word(int(f[1]), int(f[2]), f[3], [int(c) for c in f[4:]]))
    if not complete:
        sys.exit(f"{path}: the dump stops before its end line")
    words.reverse()
    seen = {}
    for w in words:
        seen[w.name] = seen.get(w.name, 0) + 1
        if seen[w.name] > 1:
            w.id = f"{w.name}#{seen[w.name]}"
    return words


def decode(cells, base, label, by_xt):
    """A thread as (cell index, op) pairs: ("call", word), ("lit", n),
    (branch kind, target cell), ("exit",). Stops at (does>)."""
    out, i = [], 0
    while i < len(cells):
        at = i
        callee = by_xt.get(cells[i])
        if callee is None:
            raise Blocked(f"undecodable cell in {label}")
        i += 1
        name = callee.name if callee.kind == 0 else None
        if name == "(does>)":
            raise Blocked("defines with DOES>")
        if name == "exit":
            out.append((at, ("exit",)))
        elif name == "lit":
            out.append((at, ("lit", cells[i])))
            i += 1
        elif name == "(s\")":                       # pushes the inline string
            n = cells[i]
            out.append((at, ("lit", base + 8 * (i + 1))))
            out.append((None, ("lit", n)))
            i += 1 + (n + 7) // 8
        elif name in BRANCHES:
            target, rem = divmod(cells[i] - base, 8)
            if rem or not 0 <= target <= len(cells):
                raise Blocked(f"branch out of {label}")
            out.append((at, (BRANCHES[name], target)))
            i += 1
        else:
            out.append((at, ("call", callee)))
    return out


def lean_name(ident):
    return "«" + ident + "»"


class Generator:
    def __init__(self, words):
        self.words = words
        self.by_xt = {w.xt: w for w in words}
        self.colon = [w for w in words if w.kind == 1]
        self.memo = {}                              # xt -> Lean reference, or Blocked
        self.open = set()
        self.defs = []                              # Lean definitions, callees first
        self.loops = 0
        self.loopy = set()                          # words that run a loop
        self.deep = False

    def ref(self, w):
        """The Lean term for a word, defining it (and its callees) first."""
        if w.xt in self.memo:
            if isinstance(self.memo[w.xt], Blocked):
                raise self.memo[w.xt]
            return self.memo[w.xt]
        if w.xt in self.open:
            raise Blocked("recursion")
        self.open.add(w.xt)
        try:
            self.memo[w.xt] = self.define(w)
        except Blocked as e:
            self.memo[w.xt] = e
            raise
        finally:
            self.open.discard(w.xt)
        return self.memo[w.xt]

    def define(self, w):
        if w.name in OVERRIDES:
            return OVERRIDES[w.name]
        if w.kind == 0:
            if w.name in PRIMS:
                return PRIMS[w.name]
            if w.name in KCONST:
                return f'(kconst "{w.name}")'
            raise Blocked(f"primitive {w.name}")
        if w.kind == 2:
            return self.emit(w.id, "constant", f"pushConst {w.cells[0]}")
        if w.kind == 3:
            return self.emit(w.id, "variable", f"pushConst {w.xt + 8}")
        if w.kind == 4:
            code = self.does_code(w)
            self.deep = code in self.loopy
            return self.emit(w.id, "DOES> child", f"doesChild {w.xt + 8} {code}")
        return self.emit(w.id, "colon", self.thread(w.cells, w.xt + 8, w.id))

    def does_code(self, child):
        """The DOES> code a child runs: the thread after "mov x9, x30; bl dodoes"."""
        target = child.cells[0] if child.cells else 0
        for p in self.colon:
            base = p.xt + 8
            if base <= target < base + 8 * len(p.cells):
                j = (target - base) // 8
                does = self.by_xt.get(p.cells[j - 1]) if j else None
                if not does or does.name != "(does>)":
                    break
                key = ("does", p.xt)
                if key not in self.memo:
                    try:
                        body = self.thread(p.cells[j + 1:], target + 8, f"does:{p.id}")
                        self.memo[key] = self.emit(f"does:{p.id}", "DOES> code", body)
                    except Blocked as e:
                        self.memo[key] = e
                if isinstance(self.memo[key], Blocked):
                    raise self.memo[key]
                return self.memo[key]
        raise Blocked("DOES> code not in a colon word")

    def thread(self, cells, base, label):
        ops = decode(cells, base, label, self.by_xt)
        index = {at: n for n, (at, _) in enumerate(ops) if at is not None}
        index[len(cells)] = len(ops)
        loops, deep, parts = False, False, []
        for n, (at, op) in enumerate(ops):
            if op[0] == "exit":
                parts.append(".exit")
            elif op[0] == "lit":
                parts.append(f".lit {op[1]}")
            elif op[0] == "call":
                callee = self.ref(op[1])
                deep |= callee in self.loopy
                parts.append(f".call {callee}")
            else:
                if op[1] not in index:
                    raise Blocked(f"branch into an operand in {label}")
                t = index[op[1]]
                loops |= t <= n or op[0] in ("qdo", "loop", "ploop")
                parts.append(f".{op[0]} {t}")
        self.loops += loops
        self.deep = loops or deep
        return ("loopThread" if loops else "thread") + " [" + ", ".join(parts) + "]"

    def emit(self, ident, what, body):
        if body.startswith("loopThread"):           # proofs about loops need the thread
            code = body[len("loopThread "):]
            self.defs.append(f"@[forth] def {lean_name(ident)}.code : List Ins := {code}\n")
            self.defs.append(f"/-- {what} -/\ndef {lean_name(ident)} : Sem := loopThread {lean_name(ident)}.code\n")
        else:
            self.defs.append(f"/-- {what} -/\n@[forth] def {lean_name(ident)} : Sem := {body}\n")
        if self.deep:                               # runs a loop, here or in a callee
            self.loopy.add(lean_name(ident))
        self.deep = False
        return lean_name(ident)


COLON = re.compile(r"(?:^|\s):\s+(\S+)(?:\s+\(\s([^)]*)\))?")


def boot_files(kernel):
    """The boot files of the hosted build, in the order kernel.s loads them."""
    files, keep = [], True
    for line in open(kernel):
        f = line.split()
        if f[:2] == [".ifdef", "HOSTED"] or f[:1] == [".endif"]:
            keep = True
        elif f[:1] == [".else"]:
            keep = False
        elif f[:1] == ["bootfile"] and keep:
            files.append(f[1].strip('"'))
    return files


def stack_effect(comment):
    """(inputs, outputs) of a plain stack comment, or None if it is not one."""
    if comment is None:
        return None
    f = comment.split()
    if f.count("--") != 1 or any(t in ("|", "R:", "C:", "...") or '"' in t or "*" in t for t in f):
        return None
    k = f.index("--")
    return k, len(f) - k - 1


def effects(gen, kernel):
    """A theorem per colon word whose stack comment states a plain effect."""
    source = {}                                     # name -> comments, in loading order
    for path in boot_files(kernel):
        for line in open(path):
            if line.lstrip().startswith("\\"):
                continue
            for m in COLON.finditer(line):
                source.setdefault(m.group(1), []).append(m.group(2))
    dumped = {}
    for w in gen.colon:
        dumped.setdefault(w.name, []).append(w)
    out, skipped = [], Counter()
    for name, ws in dumped.items():
        comments = source.get(name, [])
        if len(comments) != len(ws):
            skipped["source and dictionary disagree"] += len(ws)
            continue
        for w, comment in zip(ws, comments):
            ref = gen.memo.get(w.xt)
            effect = stack_effect(comment)
            if ref is None or isinstance(ref, Blocked):
                continue
            if effect is None:
                skipped["no plain stack comment"] += 1
            elif ref in gen.loopy:
                skipped["runs a loop"] += 1
            else:
                ins, outs = effect
                xs = " ".join(f"x{i}" for i in range(ins))
                stack = "".join(f"x{i} :: " for i in range(ins)) + "s"
                binders = f"({xs} : Cell) " if ins else ""
                out.append(f"/-- `{name}` ( {comment.strip()} ) -/\n"
                           f"theorem {lean_name(w.id + ':effect')} {binders}(s r : List Cell) (m : Mem) (u : Cell) (e : Nat) :\n"
                           f"    Effect ({ref} ⟨{stack}, r, m, u, e⟩) s r u {outs} := by forth_effect\n")
    return out, skipped


def main():
    args = sys.argv[1:]
    words_path, out_path = args[:2]
    check = []
    if "--require" in args:                         # a file of words the proofs use
        for line in open(args[args.index("--require") + 1]):
            check += line.split("\\")[0].split()
    gen = Generator(load(words_path))
    reasons = Counter()
    for w in gen.words:
        try:
            gen.ref(w)
        except Blocked as e:
            if w.kind == 1:
                reasons[str(e)] += 1

    lines = [
        "-- Generated by tools/forth2lean.py from the hosted build's dictionary",
        "-- (make proofs-extract). Do not edit; change the Forth and regenerate.",
        "import OS4.Machine",
        "",
        "namespace OS4.Words",
        "open OS4",
        "noncomputable section",
        "",
    ] + gen.defs + ["end", "end OS4.Words"]
    open(out_path, "w", newline="\n").write("\n".join(lines) + "\n")

    done = sum(1 for w in gen.colon if not isinstance(gen.memo.get(w.xt), Blocked))
    print(f"{out_path}: {done} of {len(gen.colon)} colon words ({gen.loops} threads with loops)")
    print("left out, by what blocks them first:")
    for r, n in reasons.most_common(12):
        print(f"  {n:4}  {r}")
    if "--effects" in args:                         # stack-comment theorems
        path = args[args.index("--effects") + 1]
        theorems, skipped = effects(gen, "arch/aarch64/kernel.s")
        lines = [
            "-- Generated by tools/forth2lean.py: each word's stack comment, as a theorem.",
            "-- Do not edit; change the Forth and regenerate.",
            "import OS4.Words",
            "",
            "namespace OS4.Effects",
            "open OS4 OS4.Words",
            "",
        ] + theorems + ["end OS4.Effects"]
        open(path, "w", newline="\n").write("\n".join(lines) + "\n")
        print(f"{path}: {len(theorems)} stack-comment theorems; not stated:")
        for r, n in skipped.most_common():
            print(f"  {n:4}  {r}")
    by_id = {w.id: w for w in gen.words}
    missing = [c for c in check if c not in by_id or isinstance(gen.memo.get(by_id[c].xt), Blocked)]
    if missing:
        sys.exit(f"not modelled: {' '.join(missing)}")


if __name__ == "__main__":
    main()
