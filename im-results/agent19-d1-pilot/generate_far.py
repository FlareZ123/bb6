#!/usr/bin/env python3
"""Emit a Lean-checkable Raw47 cut with FAR5 leaves closed by explicit automata."""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
tree = json.loads((ROOT / "Raw47-cut.json").read_text())
opens = (ROOT / "Raw47-open.txt").read_text().splitlines()
far_path = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / "Raw47-far5.txt"
out_path = Path(sys.argv[2]) if len(sys.argv) > 2 else ROOT / "Raw47Far5Cut.lean"

def collect_open(t, out):
    if t[0] == "open":
        out.append(t[1])
    elif t[0] == "split":
        for child in t[3]:
            collect_open(child, out)

tree_opens = []
collect_open(tree, tree_opens)
assert tree_opens == opens, "tree/open manifest mismatch"
assert len(opens) == 114, len(opens)
assert len(set(opens)) == len(opens), "duplicate open table"

bank = {}
for line in far_path.read_text().splitlines():
    if not line.strip():
        continue
    fields = line.split()
    assert len(fields) == 2, fields
    idx, code = int(fields[0]), fields[1]
    assert 0 <= idx < len(opens), idx
    assert idx not in bank, idx
    bank[idx] = code

def show(p):
    return "_".join("".join(p[i:i+2]) for i in range(0, 12, 2))

def move(i):
    return f"{i // 12}{'R' if i % 12 >= 6 else 'L'}{chr(65 + i % 6)}"

def slot(i):
    return f"({i // 2},{'true' if i % 2 else 'false'})"

def far(code, p):
    rev = int(code[0])
    D = list(map(int, code[1:]))
    n = len(D) // 2
    assert len(D) == 2 * n and 1 <= n <= 5, code
    N, H = 6 * n + 1, 6 * n
    halt = 1 << H
    T = [0] * (2 * N)
    T[H] = T[N + H] = halt
    rules = []
    for l in range(n):
        for q in range(6):
            for a in range(2):
                m = p[2 * q + a]
                dst = a * N + 6 * l + q
                if m == "---":
                    T[dst] = halt
                    continue
                w, right, k = int(m[0]), m[1] == "R", ord(m[2]) - 65
                if right != bool(rev):
                    T[dst] = 1 << (6 * D[2 * l + w] + k)
                else:
                    for j in range(n):
                        for b in range(2):
                            if D[2 * j + b] == l:
                                rules.append((dst, b * N + 6 * j + k, w * N))
    while True:
        z = halt
        while True:
            old = z
            for j in range(N):
                if T[j] & z:
                    z |= 1 << j
            assert not (z & 1), (code, show(p))
            if old == z:
                break
        changed = False
        for dst, src, off in rules:
            v, bits = T[dst], T[src]
            while bits:
                k = (bits & -bits).bit_length() - 1
                v |= T[off + k]
                bits &= bits - 1
            if v != T[dst]:
                T[dst] = v
                changed = True
        if not changed:
            return f".far {'true' if rev else 'false'} {n} ⟨0,{D},{T[:N]},{T[N:]},{z}⟩"

def emit(t, p):
    kind = t[0]
    if kind == "alias":
        return ".unresolved"
    if kind == "open":
        assert t[1] == show(p), (t[1], show(p))
        code = bank.get(opens.index(t[1]))
        return f".closed ({far(code, p)})" if code is not None else ".unresolved"
    if kind == "cycle":
        return f".closed (.cycle {t[1]} {t[2]} {'true' if t[3] else 'false'} ({t[4]}))"
    if kind == "last":
        return f".closed (.last {t[1]} {slot(t[2])})"
    if kind == "split":
        n, s, children = t[1:]
        assert len(children) == 24 and p[s] == "---", (s, p)
        emitted = []
        for i, child in enumerate(children):
            child_p = p.copy()
            child_p[s] = move(i)
            emitted.append(emit(child, child_p))
        nl = chr(10)
        return f".split {n} {slot(s)} (byPartialMove [{nl}" + ("," + nl).join(emitted) + f"{nl}])"
    raise ValueError(kind)

parent_text = "1RB---_1RC---_0RD---_1LD0RC_------_------"
parent = parent_text.replace("_", "")
parent = [parent[i:i+3] for i in range(0, 36, 3)]
source = (ROOT / "Raw47Far5.template").read_text()
source = source.replace("@@TREE@@", emit(tree, parent))
source = source.replace("@@OPEN_COUNT@@", str(len(opens) - len(bank)))
out_path.write_text(source)
root_template = ROOT / "Raw47Far5RootRefinement.template"
(ROOT / "Raw47Far5RootRefinement.lean").write_text(root_template.read_text())
print(f"Raw47 FAR5: {len(bank)}/{len(opens)} leaves certified; {len(opens)-len(bank)} canonical residuals")
