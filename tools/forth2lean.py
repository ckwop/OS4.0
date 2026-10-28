#!/usr/bin/env python3
"""Generate Lean definitions of Forth words from the dictionary as compiled.

Reads the dump that tools/dump-words.fs prints (make proofs-extract), takes the
words named in a roots file and everything they call, and writes a Lean module
defining each one over the primitives in proofs/OS4/Machine.lean. Proofs are
about these definitions, so changing a word's Forth changes what is proven.

Words are named as in Forth. A name defined more than once gets #2, #3 ... on
its later definitions, oldest first ("allot#2"), and a root must say which.

Fails, rather than skipping, on anything it cannot represent: an operand it
does not know, a backward branch (loops are not modelled yet), recursion.

Usage: forth2lean.py words.txt roots.txt Words.lean
"""

import sys

# Primitives the model defines, by Forth name.
PRIMS = {
    "dup": "Prim.dup", "drop": "Prim.drop", "swap": "Prim.swap", "over": "Prim.over",
    ">r": "Prim.tor", "r>": "Prim.rfrom", "r@": "Prim.rfetch", "pick": "Prim.pick",
    "+": "Prim.plus", "-": "Prim.minus", "*": "Prim.star", "/mod": "Prim.slashmod",
    "and": "Prim.and", "or": "Prim.or", "xor": "Prim.xor", "invert": "Prim.invert",
    "lshift": "Prim.lshift", "rshift": "Prim.rshift",
    "=": "Prim.equal", "<": "Prim.less", "u<": "Prim.uless",
    "0=": "Prim.zequal", "0<": "Prim.zless",
}
# Primitives followed in a thread by an operand cell.
BRANCHES = {"branch": "branch", "0branch": "zbranch"}
OPERANDS = {"lit", "branch", "0branch", "(?do)", "(loop)", "(+loop)", "(does>)", "(s\")"}
KINDS = {0: "primitive", 1: "colon", 2: "constant", 3: "variable", 4: "does"}


class Word:
    def __init__(self, xt, kind, name, cells):
        self.xt, self.kind, self.name, self.cells = xt, kind, name, cells
        self.id = name


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


def decode(w, by_xt):
    """A colon word's thread as (op, arg) pairs: call word, lit n, branch i."""
    body, out, i = w.xt + 8, [], 0
    while i < len(w.cells):
        callee = by_xt.get(w.cells[i])
        if callee is None:
            sys.exit(f"{w.id}: cell {i} ({w.cells[i]}) is not a word: an operand this tool does not know?")
        i += 1
        if callee.name not in OPERANDS:
            out.append(("exit", None) if callee.name == "exit" else ("call", callee))
            continue
        if callee.name not in ("lit",) + tuple(BRANCHES):
            sys.exit(f"{w.id}: uses {callee.name}, which the model does not support yet")
        arg = w.cells[i]
        i += 1
        if callee.name == "lit":
            out.append(("lit", arg))
            continue
        target, rem = divmod(arg - body, 8)
        if rem or not 0 <= target <= len(w.cells):
            sys.exit(f"{w.id}: branch out of the thread")
        if target <= i - 2:
            sys.exit(f"{w.id}: backward branch (a loop): not modelled yet")
        out.append((BRANCHES[callee.name], None, target))
    return out


def index_of(ops):
    """Cell index -> instruction index, as operands take a cell but no instruction."""
    m, cell = {}, 0
    for n, op in enumerate(ops):
        m[cell] = n
        cell += 2 if op[0] in ("lit", "branch", "zbranch") else 1
    m[cell] = len(ops)
    return m


def lean_name(w):
    return "«" + w.id + "»"


def main():
    words_path, roots_path, out_path = sys.argv[1:4]
    words = load(words_path)
    by_xt = {w.xt: w for w in words}
    by_id = {w.id: w for w in words}
    counts = {}
    for w in words:
        counts[w.name] = counts.get(w.name, 0) + 1

    roots = []
    for line in open(roots_path):
        line = line.split("\\")[0].strip()
        for r in line.split():
            if r not in by_id:
                sys.exit(f"{roots_path}: no word {r}")
            if counts[r] > 1:
                sys.exit(f"{roots_path}: {r} is defined {counts[r]} times; name one as {r}#n")
            roots.append(by_id[r])

    order, state, decoded = [], {}, {}

    def visit(w, path):
        if state.get(w.xt) == "done":
            return
        if state.get(w.xt) == "open":
            sys.exit(f"recursion: {' -> '.join(p.id for p in path + [w])}")
        state[w.xt] = "open"
        if w.kind == 1 and w.name not in PRIMS:
            decoded[w.xt] = decode(w, by_xt)
            for op in decoded[w.xt]:
                if op[0] == "call":
                    visit(op[1], path + [w])
        state[w.xt] = "done"
        order.append(w)

    for r in roots:
        visit(r, [])

    lines = [
        "-- Generated by tools/forth2lean.py from the hosted build's dictionary",
        "-- (make proofs-extract): the words in proofs/roots.txt and all they call.",
        "-- Do not edit; change the Forth and regenerate.",
        "import OS4.Machine",
        "",
        "namespace OS4.Words",
        "open OS4",
        "",
    ]
    for w in order:
        if w.name in PRIMS and w.kind == 0:
            continue                                    # referred to as Prim.*
        if w.kind == 2:
            body = f"pushConst {w.cells[0]}"
        elif w.kind == 1:
            ops = decoded[w.xt]
            idx = index_of(ops)
            parts = []
            for op in ops:
                if op[0] == "exit":
                    parts.append(".exit")
                elif op[0] == "lit":
                    parts.append(f".lit {op[1]}")
                elif op[0] == "call":
                    parts.append(f".call {ref(op[1])}")
                else:
                    parts.append(f".{op[0]} {idx[op[2]]}")
            body = "thread [" + ", ".join(parts) + "]"
        else:
            body = f'unmodelled "{w.id}"'
        lines.append(f"/-- {KINDS[w.kind]} -/")
        lines.append(f"@[forth] def {lean_name(w)} : Sem := {body}")
        lines.append("")
    lines.append("end OS4.Words")
    open(out_path, "w", newline="\n").write("\n".join(lines) + "\n")
    print(f"{out_path}: {len(order)} words from {len(roots)} roots")


def ref(w):
    if w.kind == 0 and w.name in PRIMS:
        return PRIMS[w.name]
    if w.kind == 0:
        return f'(unmodelled "{w.id}")'
    return lean_name(w)


if __name__ == "__main__":
    main()
