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
# Stack effects of the primitives, as proven in proofs/OS4/PrimSpecs.lean:
# (data in, data out, return in, return out).
EFFECTS = {
    "dup": (1, 2, 0, 0), "drop": (1, 0, 0, 0), "swap": (2, 2, 0, 0), "over": (2, 3, 0, 0),
    "tor": (1, 0, 0, 1), "rfrom": (0, 1, 1, 0), "rfetch": (0, 1, 1, 1), "pick": (1, 1, 0, 0),
    "depth": (0, 1, 0, 0), "plus": (2, 1, 0, 0), "minus": (2, 1, 0, 0), "star": (2, 1, 0, 0),
    "and": (2, 1, 0, 0), "or": (2, 1, 0, 0), "xor": (2, 1, 0, 0), "invert": (1, 1, 0, 0),
    "lshift": (2, 1, 0, 0), "rshift": (2, 1, 0, 0), "equal": (2, 1, 0, 0), "less": (2, 1, 0, 0),
    "uless": (2, 1, 0, 0), "zequal": (1, 1, 0, 0), "zless": (1, 1, 0, 0),
    "slashmod": (2, 2, 0, 0), "umstar": (2, 2, 0, 0), "umslashmod": (3, 2, 0, 0),
    "fetch": (1, 1, 0, 0), "store": (2, 0, 0, 0), "cfetch": (1, 1, 0, 0), "cstore": (2, 0, 0, 0),
    "wfetch": (1, 1, 0, 0), "wstore": (2, 0, 0, 0), "lfetch": (1, 1, 0, 0), "lstore": (2, 0, 0, 0),
    "cmove": (3, 0, 0, 0), "cmoveUp": (3, 0, 0, 0), "fill": (3, 0, 0, 0), "upfetch": (0, 1, 0, 0),
    "pdo": (2, 0, 0, 2), "i": (0, 1, 1, 1), "j": (0, 1, 3, 3), "unloop": (0, 0, 2, 0),
    "pause": (0, 0, 0, 0), "ask": (0, 1, 0, 0), "emit": (1, 0, 0, 0), "syscall": (5, 1, 0, 0),
    "bye": (0, 0, 0, 0), "barrier": (0, 0, 0, 0), "sha256block": (4, 0, 0, 0), "sha256out": (2, 0, 0, 0),
}
PRIM_SPECS = {f"Prim.{p}": e + (f"Prim.{p}_spec",) for p, e in EFFECTS.items()}
PRIM_SPECS["throwM"] = (1, 0, 0, 0, "throwM_spec")
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
        self.specs = dict(PRIM_SPECS)               # Lean ref -> (k, j, rk, rj, proof)
        self.thms = []                              # Spec theorems, callees first
        self.no_spec = {}                           # Lean ref -> why it has none

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
                ref = f'(kconst "{w.name}")'
                self.specs[ref] = (0, 1, 0, 0, f'(kconst_spec "{w.name}")')
                return ref
            raise Blocked(f"primitive {w.name}")
        if w.kind in (2, 3):
            value = w.cells[0] if w.kind == 2 else w.xt + 8
            name = self.emit(w.id, KINDS[w.kind], f"pushConst {value}")
            self.prove(name, (0, 1, 0, 0), "pushConst_spec _")
            return name
        if w.kind == 4:
            code = self.does_code(w)
            self.deep = code in self.loopy
            name = self.emit(w.id, "DOES> child", f"doesChild {w.xt + 8} {code}")
            if code in self.specs:                  # push the body, then run the code
                k, j, rk, rj, proof = self.specs[code]
                if k:
                    self.prove(name, (k - 1, j, rk, rj), f"doesChild_spec _ {proof}")
                else:
                    self.prove(name, (0, j + 1, rk, rj), f"doesChild_spec _ (spec_frame {proof} 1)")
            return name
        return self.emit_thread(w.id, "colon", *self.thread(w.cells, w.xt + 8, w.id))

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
                        loops, insns = self.thread(p.cells[j + 1:], target + 8, f"does:{p.id}")
                        self.memo[key] = self.emit_thread(f"does:{p.id}", "DOES> code", loops, insns)
                    except Blocked as e:
                        self.memo[key] = e
                if isinstance(self.memo[key], Blocked):
                    raise self.memo[key]
                return self.memo[key]
        raise Blocked("DOES> code not in a colon word")

    def thread(self, cells, base, label):
        """(has loops, instructions): ("call", Lean ref), ("lit", n),
        (branch kind, target instruction), ("exit",)."""
        ops = decode(cells, base, label, self.by_xt)
        index = {at: n for n, (at, _) in enumerate(ops) if at is not None}
        index[len(cells)] = len(ops)
        loops, deep, insns = False, False, []
        for n, (at, op) in enumerate(ops):
            if op[0] in ("exit", "lit"):
                insns.append(op)
            elif op[0] == "call":
                callee = self.ref(op[1])
                deep |= callee in self.loopy
                insns.append(("call", callee))
            else:
                if op[1] not in index:
                    raise Blocked(f"branch into an operand in {label}")
                t = index[op[1]]
                loops |= t <= n or op[0] in ("qdo", "loop", "ploop")
                insns.append((op[0], t))
        self.loops += loops
        self.deep = loops or deep
        return loops, insns

    def emit_thread(self, ident, what, loops, insns):
        """A thread's code and word, and its Spec if its depths check out."""
        name = lean_name(ident)
        parts = []
        for op in insns:
            if op[0] == "exit":
                parts.append(".exit")
            elif op[0] == "lit":
                parts.append(f".lit {op[1]}")
            elif op[0] == "call":
                parts.append(f".call {op[1]}")
            else:
                parts.append(f".{op[0]} {op[1]}")
        self.defs.append(f"@[forth] noncomputable def {name}.code : List Ins := [{', '.join(parts)}]\n")
        runner = "loopThread" if loops else "thread"
        attr = "" if loops else "@[forth] "
        self.defs.append(f"/-- {what} -/\n{attr}noncomputable def {name} : Sem := {runner} {name}.code\n")
        if self.deep:                               # runs a loop, here or in a callee
            self.loopy.add(name)
        self.deep = False
        found = self.infer(insns)
        if isinstance(found, str):
            self.no_spec[name] = found
        else:
            k, j, certs = found
            calls = "True.intro"
            for op in reversed(insns):
                calls = f"And.intro {self.specs[op[1]][4] if op[0] == 'call' else 'True.intro'} ({calls})"
            self.thms.append(f"noncomputable def {name}.cert : List Cert := [{', '.join(certs)}]\n")
            self.prove(name, (k, j, 0, 0),
                       f"{runner}_spec (code := {name}.code) (cert := {name}.cert)\n"
                       f"    (by decide)\n    ({calls})")
        return name

    def emit(self, ident, what, body):
        self.defs.append(f"/-- {what} -/\n@[forth] noncomputable def {lean_name(ident)} : Sem := {body}\n")
        if self.deep:
            self.loopy.add(lean_name(ident))
        self.deep = False
        return lean_name(ident)

    def prove(self, name, effect, proof):
        """State and prove a word's Spec; later words' proofs use it."""
        k, j, rk, rj = effect
        self.specs[name] = (k, j, rk, rj, f"{name}.spec")
        self.thms.append(f"theorem {name}.spec : Spec {name} {k} {j} {rk} {rj} :=\n  {proof}\n")

    def infer(self, insns):
        """The depths of both stacks before each instruction, relative to the
        word's floor: (inputs, outputs, certificate entries), or why not."""
        state, work, low, exits = {0: (0, 0)}, [0], 0, set()
        while work:
            pc = work.pop()
            d, r = state[pc]
            op = insns[pc]
            if op[0] == "exit":
                exits.add((d, r))
                continue
            if op[0] == "call":
                if op[1] not in self.specs:
                    return "calls a word with no Spec"
                k, j, rk, rj, _ = self.specs[op[1]]
                if r < rk:
                    return "takes return-stack items it did not push"
                low = min(low, d - k)
                succ = [(pc + 1, d - k + j, r - rk + rj)]
            elif op[0] == "lit":
                succ = [(pc + 1, d + 1, r)]
            elif op[0] == "branch":
                succ = [(op[1], d, r)]
            elif op[0] == "zbranch":
                low = min(low, d - 1)
                succ = [(op[1], d - 1, r), (pc + 1, d - 1, r)]
            elif op[0] == "qdo":
                low = min(low, d - 2)
                succ = [(op[1], d - 2, r), (pc + 1, d - 2, r + 2)]
            elif op[0] == "loop":
                if r < 2:
                    return "LOOP without its parameters"
                succ = [(op[1], d, r), (pc + 1, d, r - 2)]
            else:                                   # ploop
                if r < 2:
                    return "+LOOP without its parameters"
                low = min(low, d - 1)
                succ = [(op[1], d - 1, r), (pc + 1, d - 1, r - 2)]
            for t, nd, nr in succ:
                if t >= len(insns):
                    return "runs off its end"
                if t not in state:
                    state[t] = (nd, nr)
                    work.append(t)
                elif state[t] != (nd, nr):
                    return "paths meet with different depths"
        if len(exits) != 1:
            return "exits with different depths"
        dx, rx = exits.pop()
        if rx:
            return "leaves items on the return stack"
        certs = []
        for pc, op in enumerate(insns):
            if pc not in state:
                certs.append("⟨Bool.false, 0, 0, 0, 0, 0, 0⟩")
                continue
            d, r = state[pc]
            k, j, rk, rj = self.specs[op[1]][:4] if op[0] == "call" else (0, 0, 0, 0)
            certs.append(f"⟨Bool.true, {d - low}, {r}, {k}, {j}, {rk}, {rj}⟩")
        return -low, dx - low, certs


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
    return cells(f[:k]), cells(f[k + 1:])


DOUBLE = re.compile(r"^(u?d|xd)\d*'*$")


def cells(items):
    """Stack cells named in a comment: a double number (d, ud, xd) is two."""
    return sum(2 if DOUBLE.match(t) else 1 for t in items)


def comments(gen, kernel):
    """Check each plain stack comment against the word's proven Spec. A
    comment that agrees (perhaps naming items the word passes through) gets a
    theorem in its own words; one that disagrees is a finding."""
    source = {}                                     # name -> (where, comment), in loading order
    for path in boot_files(kernel):
        for n, line in enumerate(open(path), 1):
            if line.lstrip().startswith("\\"):
                continue
            for m in COLON.finditer(line):
                source.setdefault(m.group(1), []).append((f"{path}:{n}", m.group(2)))
    dumped = {}
    for w in gen.colon:
        dumped.setdefault(w.name, []).append(w)
    thms, findings, counts = [], [], Counter()
    for name, ws in dumped.items():
        defs = source.get(name, [])
        if len(defs) != len(ws):
            counts["source and dictionary disagree"] += len(ws)
            continue
        for w, (where, comment) in zip(ws, defs):
            ref = gen.memo.get(w.xt)
            effect = stack_effect(comment)
            if ref is None or isinstance(ref, Blocked):
                continue
            if effect is None:
                counts["no plain stack comment"] += 1
                continue
            if ref not in gen.specs:
                counts["no Spec"] += 1
                if ref in gen.no_spec:
                    findings.append(f"{where}: {name} ( {comment.strip()} ): no fixed effect: {gen.no_spec[ref]}")
                continue
            k, j = gen.specs[ref][:2]
            ck, cj = effect
            if ck >= k and ck - k == cj - j:
                counts["agree"] += 1
                thms.append(f"/-- `{name}` ( {comment.strip()} ) -/\n"
                            f"theorem {lean_name(w.id)}.comment : Spec {ref} {ck} {cj} 0 0 :=\n"
                            f"  spec_frame {ref}.spec {ck - k}\n")
            else:
                counts["disagree"] += 1
                findings.append(f"{where}: {name} ( {comment.strip()} ): proven ( {k} -- {j} )")
    return thms, findings, counts


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
    if "--specs" in args:                           # stack-effect theorems
        path = args[args.index("--specs") + 1]
        report = args[args.index("--findings") + 1]
        thms, findings, counts = comments(gen, "arch/aarch64/kernel.s")
        lines = [
            "-- Generated by tools/forth2lean.py: each word's stack effect, proven from",
            "-- a certificate and its callees' effects; then each agreeing stack comment.",
            "-- Do not edit; change the Forth and regenerate.",
            "import OS4.Words",
            "import OS4.PrimSpecs",
            "",
            "namespace OS4.Words",
            "open OS4",
            "",
        ] + gen.thms + thms + ["end OS4.Words"]
        open(path, "w", newline="\n").write("\n".join(lines) + "\n")
        open(report, "w", newline="\n").write("".join(f + "\n" for f in findings))
        print(f"{path}: {len(gen.thms)} stack effects proven; stack comments:")
        for r, n in counts.most_common():
            print(f"  {n:4}  {r}")
        print(f"{report}: {len(findings)} findings")
        for why, n in Counter(gen.no_spec.values()).most_common():
            print(f"  no Spec: {n:4}  {why}")
    by_id = {w.id: w for w in gen.words}
    missing = [c for c in check if c not in by_id or isinstance(gen.memo.get(by_id[c].xt), Blocked)]
    if missing:
        sys.exit(f"not modelled: {' '.join(missing)}")


if __name__ == "__main__":
    main()
