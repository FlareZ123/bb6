#!/usr/bin/env python3
"""Run FAR5 over Raw49's root open cylinders and emit a Lean-checkable partial audit."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
WORK = Path(sys.argv[1]).resolve()
OPEN_PATH = WORK / "r49.open"
TREE_PATH = WORK / "r49.json"
FAR_SOURCE = ROOT.parent / "agent19-raw40-cut" / "farbank.cpp"
FAR_BINARY = WORK / "farbank"
FAR_INPUT = WORK / "farbank.in"
FAR_PATH = WORK / "far5.txt"
FAR_LOG = WORK / "far5.log"
OUT_PATH = WORK / "Raw49Far5Cut.lean"

PARENT_TEXT = "1RB---_1RC---_0RD---_1LD1RC_------_------"
SWEEP_TABLES = {
    "1RB---_1RC---_0RD0RC_1LD1RC_------_------",
    "1RB0RC_1RC---_0RD0RA_1LD1RC_------_------",
    "1RB---_1RC0RC_0RD0RB_1LD1RC_------_------",
    "1RB---_1RC---_0RD0RE_1LD1RC_---0RC_------",
}


def show(p):
    return "_".join("".join(p[i:i+2]) for i in range(0, 12, 2))


def slot(i):
    return f"({i//2},{'true' if i%2 else 'false'})"


def move(i):
    return f"{i//12}{'R' if i%12 >= 6 else 'L'}{chr(65+i%6)}"


def far(code, p):
    rev = int(code[0])
    D = list(map(int, code[1:]))
    n = len(D) // 2
    assert len(code) == 2*n+1 and 1 <= n <= 5, code
    N, H = 6*n+1, 6*n
    halt = 1 << H
    T = [0] * (2*N)
    T[H] = T[N+H] = halt
    rules = []
    for l in range(n):
        for q in range(6):
            for a in range(2):
                mv = p[2*q+a]
                dst = a*N+6*l+q
                if mv == "---":
                    T[dst] = halt
                    continue
                w, right, k = int(mv[0]), mv[1] == "R", ord(mv[2])-65
                if right != bool(rev):
                    T[dst] = 1 << (6*D[2*l+w]+k)
                else:
                    for j in range(n):
                        for b in range(2):
                            if D[2*j+b] == l:
                                rules.append((dst, b*N+6*j+k, w*N))
    while True:
        z = halt
        while True:
            old = z
            for j in range(N):
                if T[j] & z:
                    z |= 1 << j
            if old == z:
                break
        assert not (z & 1), (code, show(p))
        changed = False
        for dst, src, off in rules:
            v, bits = T[dst], T[src]
            while bits:
                k = (bits & -bits).bit_length()-1
                v |= T[off+k]
                bits &= bits-1
            if v != T[dst]:
                T[dst] = v
                changed = True
        if not changed:
            return f".far {rev} {n} ⟨0,{D},{T[:N]},{T[N:]},{z}⟩"


def collect_open(node, out):
    if node[0] == "open":
        out.append(node[1])
    elif node[0] == "split":
        for child in node[3]:
            collect_open(child, out)


def emit(node, p, index, bank):
    kind = node[0]
    if kind == "alias":
        return ".unresolved"
    if kind == "open":
        assert node[1] == show(p), (node[1], show(p))
        idx = index[node[1]]
        code = bank.get(idx)
        return f".closed ({far(code, p)})" if code is not None else ".unresolved"
    if kind == "cycle":
        return f".closed (.cycle {node[1]} {node[2]} {'true' if node[3] else 'false'} ({node[4]}))"
    if kind == "last":
        return f".closed (.last {node[1]} {slot(node[2])})"
    if kind == "split":
        n, s, children = node[1:]
        assert len(children) == 24 and p[s] == "---", (s, p)
        emitted = []
        for i, child in enumerate(children):
            child_p = p.copy()
            child_p[s] = move(i)
            emitted.append(emit(child, child_p, index, bank))
        return f".split {n} {slot(s)} (byPartialMove [\n" + ",\n".join(emitted) + "\n])"
    raise ValueError(kind)


def main():
    assert WORK.is_dir() and OPEN_PATH.is_file() and TREE_PATH.is_file()
    subprocess.run(["g++", "-std=c++20", "-O3", str(FAR_SOURCE), "-o", str(FAR_BINARY)], check=True)
    opens = OPEN_PATH.read_text().splitlines()
    tree = json.loads(TREE_PATH.read_text())
    tree_opens = []
    collect_open(tree, tree_opens)
    assert tree_opens == opens, "Raw49 tree/open manifest mismatch"
    assert len(opens) == 125 and len(set(opens)) == len(opens), len(opens)
    assert SWEEP_TABLES <= set(opens), SWEEP_TABLES-set(opens)

    with FAR_INPUT.open("w") as f:
        for i, table in enumerate(opens):
            f.write(f"{i} {table.replace('_','')}\n")
    with FAR_INPUT.open("r") as inp, FAR_PATH.open("w") as out, FAR_LOG.open("w") as err:
        subprocess.run([str(FAR_BINARY), "5"], stdin=inp, stdout=out, stderr=err, check=True)

    bank = {}
    for line in FAR_PATH.read_text().splitlines():
        if not line.strip():
            continue
        idx_s, code = line.split()
        idx = int(idx_s)
        assert 0 <= idx < len(opens) and idx not in bank, (idx, code)
        assert len(code) % 2 == 1 and 3 <= len(code) <= 11, code
        bank[idx] = code

    index = {table: i for i, table in enumerate(opens)}
    parent = PARENT_TEXT.replace("_", "")
    parent = [parent[i:i+3] for i in range(0, 36, 3)]
    tree_expr = emit(tree, parent, index, bank)

    unresolved = [table for i, table in enumerate(opens) if i not in bank]
    remaining = [table for table in unresolved if table not in SWEEP_TABLES]
    child_tables = {opens[i] for i in (0, 2, 5)}
    after_children = [table for table in remaining if table not in child_tables]
    canonical_count = len(unresolved)
    remaining_count = len(remaining)
    after_children_count = len(after_children)
    assert canonical_count == len(opens)-len(bank)
    assert remaining_count == len(opens)-len(set(bank_table for bank_table in [opens[i] for i in bank]) | SWEEP_TABLES)
    assert after_children_count == len(opens)-len(set([opens[i] for i in bank]) | SWEEP_TABLES | child_tables)

    module = f"""import Raw49Cut

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw49Far5Cut
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent7Raw49Cut

def tree : PartialAudit := {tree_expr}

theorem canonical_checked : canonicalCheck 7014 BB6.Agent7Raw49Cut.parent 4 tree = true := by decide

def canonicalRemaining := canonicalResiduals BB6.Agent7Raw49Cut.parent 4 tree
def remaining := canonicalRemaining.filter (fun e => !BB6.Agent7Raw49Cut.sweepMatch e.2)

theorem canonical_count : canonicalRemaining.length = {canonical_count} := by decide
theorem remaining_count : remaining.length = {remaining_count} := by decide

/-- Exact residual count after FAR5, the four sweeps, and complete C0/C2/C5 child Covers. -/
def expected_after_children : Nat := {after_children_count}

theorem canonical_local_sound : ∀ m, TNFQuotientCompatible BB6.Agent7Raw49Cut.parent m →
    WeightedBound 7014 m ∨ ∃ e ∈ remaining, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases canonicalSound 7014 BB6.Agent7Raw49Cut.parent 4 tree (by decide)
      BB6.Agent7Raw49Cut.supported BB6.Agent7Raw49Cut.root BB6.Agent7Raw49Cut.nohalt canonical_checked m hm with h | ⟨e,he,hq⟩
  · exact Or.inl h
  · cases hh : BB6.Agent7Raw49Cut.sweepMatch e.2 with
    | false => exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [hh]⟩,hq⟩
    | true =>
      obtain ⟨k,hk,hmatch⟩ := List.any_eq_true.mp hh
      have heq := BB6.Agent7Raw49Cut.equalTable_sound hmatch
      rw [heq] at hq
      exact Or.inl (quotientSafe (BB6.Agent7Raw49Cut.sweepRoot k)
        (BB6.Agent7Raw49Cut.sweepWeighted k) m hq)

theorem parent_cut (m : Machine) (hm : TNFQuotientCompatible BB6.Agent7Raw49Cut.parent m) :
    WeightedBound 7014 m ∨ ∃ e ∈ remaining, TNFQuotientCompatible e.2 m :=
  canonical_local_sound m hm

#print axioms canonical_checked
#print axioms canonical_local_sound
#print axioms parent_cut
#print axioms canonical_count
#print axioms remaining_count
end BB6.Agent7Raw49Far5Cut
"""
    OUT_PATH.write_text(module)
    summary = {
        "parent": PARENT_TEXT,
        "bound": 7014,
        "open_count": len(opens),
        "far5_count": len(bank),
        "canonical_residual_count": canonical_count,
        "after_sweeps_count": remaining_count,
        "after_C0_C2_C5_count": after_children_count,
        "far5_sha256": hashlib.sha256(FAR_PATH.read_bytes()).hexdigest(),
        "open_sha256": hashlib.sha256(OPEN_PATH.read_bytes()).hexdigest(),
    }
    (WORK / "far5-summary.json").write_text(json.dumps(summary, indent=2)+"\n")
    print("Raw49 FAR5 summary:", json.dumps(summary, sort_keys=True))
    output = os.environ.get("GITHUB_OUTPUT")
    if output:
        with open(output, "a") as f:
            f.write(f"far5_count={len(bank)}\n")
            f.write(f"remaining_count={remaining_count}\n")
            f.write(f"after_children_count={after_children_count}\n")
    print(FAR_LOG.read_text())


if __name__ == "__main__":
    main()
