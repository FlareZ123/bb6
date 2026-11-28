#!/usr/bin/env python3
"""Generate a compact Lean source replay of the Raw54 E1=1RD FAR-pruned tree.

The C++ discovery tree is untrusted.  Every terminal and split is rechecked by
Raw54OneRDBankAudit.lean; FAR leaves store only the exact bank index and Lean
reruns fastTryDfa for that source-derived DFA.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

PARENT_SPEC = "1RB---_1RC---_0RD---_1LD0LE_---1RD_------"
BOUND = 1006
NS = "BB6.Agent8Raw54.OneRDBankAudit"


def move(i: int) -> str:
    return str(i // 12) + ("R" if i % 12 >= 6 else "L") + chr(65 + i % 6)


def mv(i: int) -> str:
    return f"⟨{str(i >= 12).lower()},{str(i % 12 >= 6).lower()},{i % 6}⟩"


def slot(i: int) -> str:
    return f"({i // 2},{str(bool(i % 2)).lower()})"


def parse_spec(spec: str) -> tuple[int, ...]:
    s = spec.replace("_", "")
    assert len(s) == 36
    out = []
    for i in range(0, 36, 3):
        if s[i] == "-":
            out.append(-1)
        else:
            out.append(int(s[i]) * 12 + (6 if s[i + 1] == "R" else 0) + ord(s[i + 2]) - 65)
    return tuple(out)


def show(p: tuple[int, ...]) -> str:
    parts = []
    for i, x in enumerate(p):
        if i and i % 2 == 0:
            parts.append("_")
        parts.append("---" if x < 0 else move(x))
    return "".join(parts)


def refine(p: tuple[int, ...], s: int, i: int) -> tuple[int, ...]:
    return p[:s] + (i,) + p[s + 1 :]


def decode_digit(c: str) -> int:
    if "0" <= c <= "9":
        return ord(c) - ord("0")
    if "a" <= c <= "z":
        return ord(c) - ord("a") + 10
    raise ValueError(c)


def parse_bank(path: Path) -> list[tuple[bool, int, list[int]]]:
    codes = path.read_text().split()
    out = []
    for code in codes:
        assert code[0] in "01"
        raw = [decode_digit(c) for c in code[1:]]
        assert raw and len(raw) % 2 == 0
        d = len(raw) // 2
        assert all(0 <= x < d for x in raw), (code, d, max(raw))
        out.append((code[0] == "1", d, raw))
    assert len(out) == 169, len(out)
    return out


def tree_size(t) -> int:
    return 1 + sum(tree_size(x) for x in t[3]) if t[0] == "split" else 1


def residual_stats(t, p: tuple[int, ...]) -> tuple[int, int]:
    """Exact unresolved-node count and physical completion mass below t."""
    if t[0] == "open":
        assert t[1] == show(p), (t[1], show(p))
        return 1, 25 ** sum(x < 0 for x in p)
    if t[0] == "split":
        _, s, kids = int(t[1]), int(t[2]), t[3]
        n = mass = 0
        for i, child in enumerate(kids):
            cn, cm = residual_stats(child, refine(p, s, i))
            n += cn
            mass += cm
        return n, mass
    return 0, 0


def render_tree(t, p: tuple[int, ...], bank_count: int, open_seen: list[str]) -> str:
    kind = t[0]
    if kind == "far":
        i, holes = int(t[1]), int(t[2])
        assert 0 <= i < bank_count
        assert holes == sum(x < 0 for x in p), (holes, p)
        return f".far {i}"
    if kind == "cycle":
        return f".cycle {t[1]} {t[2]} {str(bool(t[3])).lower()} ({t[4]})"
    if kind == "last":
        n, s = int(t[1]), int(t[2])
        assert p[s] < 0
        return f".last {n} {slot(s)}"
    if kind == "open":
        code = t[1]
        assert code == show(p), (code, show(p))
        open_seen.append(code)
        return ".unresolved"
    if kind == "split":
        n, s, kids = int(t[1]), int(t[2]), t[3]
        assert p[s] < 0 and len(kids) == 24
        body = ",".join(render_tree(x, refine(p, s, i), bank_count, open_seen) for i, x in enumerate(kids))
        return f".split {n} {slot(s)} (byBankMove [{body}])"
    raise ValueError(t)


def combine_proof(name: str, pexpr: str, n: int, s: int, child_names: list[str]) -> str:
    lines = [
        f"def {name} : BankAudit := .split {n} {slot(s)} (byBankMove [{','.join(child_names)}])\n",
        f"theorem {name}_checked : bankCheck bank B {pexpr} {name} = true := by\n",
        f"  rw [{name},bankCheck]\n",
        "  simp only [Bool.and_eq_true]\n",
        "  refine ⟨by decide +kernel,allMoves_of _ ?_⟩\n",
        "  intro z\n",
        "  rcases z with ⟨w,r,q⟩\n",
        "  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega\n",
        "  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl\n",
        "  all_goals cases w <;> cases r\n",
    ]
    # Goal order after q split, then write/right cases, is q-major with each
    # Bool case expansion. The same order is used by byBankMove's numeric code.
    for q in range(6):
        for w, r in [(0, 0), (0, 1), (1, 0), (1, 1)]:
            i = 12 * w + 6 * r + q
            lines.append(f"  · exact {child_names[i]}_checked\n")
    return "".join(lines)


def emit_subtree(t, p: tuple[int, ...], pexpr: str, ident: str, parts: list[str],
                 bank_count: int, open_seen: list[str], threshold: int = 96) -> str:
    name = "t" + ident
    if t[0] == "split" and tree_size(t) > threshold:
        n, s, kids = int(t[1]), int(t[2]), t[3]
        assert p[s] < 0 and len(kids) == 24
        children = []
        for i, child in enumerate(kids):
            cp = refine(p, s, i)
            ce = f"(refine {pexpr} {slot(s)} (some {mv(i)}))"
            children.append(emit_subtree(child, cp, ce, ident + f"_{i:02d}", parts,
                                         bank_count, open_seen, threshold))
        parts.append(combine_proof(name, pexpr, n, s, children))
    else:
        lit = render_tree(t, p, bank_count, open_seen)
        parts.append(f"def {name} : BankAudit := {lit}\n")
        parts.append(
            f"theorem {name}_checked : bankCheck bank B {pexpr} {name} = true := by decide +kernel\n"
        )
    return name


def write_bank(out: Path, bank: list[tuple[bool, int, list[int]]]) -> None:
    entries = []
    for rev, d, raw in bank:
        entries.append(
            f"⟨{str(rev).lower()},{d},by decide,{json.dumps(raw, separators=(',', ':'))}⟩"
        )
    src = f"""import Raw54OneRDBankAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {NS}
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10FastAudit

abbrev parent : PartialMachine := refine BB6.Agent8Raw54.raw54 (4,true) (some ⟨true,true,3⟩)
def B : Nat := {BOUND}

theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide +kernel

private theorem raw54_nohalt : weightedTNFNoAssignedHalt BB6.Agent8Raw54.raw54 :=
  weightedTNFNoAssignedHalt_refine _ _ _
    (pathEnd_nohalt root 2 (path.take 3) firstOneCylinder_no_assigned_halt)

theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  weightedTNFNoAssignedHalt_refine _ _ _ raw54_nohalt

def bank : List FarSpec := [{','.join(entries)}]

theorem bank_length : bank.length = 169 := by decide +kernel

#print axioms parent_nohalt
#print axioms bank_length
end {NS}
"""
    (out / "Raw54OneRDBank.lean").write_text(src)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("discovery", type=Path)
    ap.add_argument("out", type=Path)
    ap.add_argument("--threshold", type=int, default=96)
    args = ap.parse_args()
    discovery, out = args.discovery.resolve(), args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)

    bank = parse_bank(out / "oneRD_leancert_bank.txt")
    tree = json.loads((discovery / "tree.json").read_text())
    opens = (discovery / "open.txt").read_text().splitlines()
    assert tree[0] == "split", tree[0]
    n, s, kids = int(tree[1]), int(tree[2]), tree[3]
    assert len(kids) == 24

    write_bank(out, bank)
    parent = parse_spec(PARENT_SPEC)
    seen: list[str] = []
    branch_names = []
    for i, child in enumerate(kids):
        mod = f"Raw54OneRDBranch{i:02d}"
        bns = f"{NS}.Branch{i:02d}"
        p = refine(parent, s, i)
        pexpr = f"(refine {NS}.parent {slot(s)} (some {mv(i)}))"
        parts = [
            "import Raw54OneRDBank\n",
            "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n",
            f"namespace {bns}\n",
            f"open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10FastAudit {NS}\n",
        ]
        root_name = emit_subtree(child, p, pexpr, f"b{i:02d}", parts, len(bank), seen, args.threshold)
        rn, _rm = residual_stats(child, p)
        parts.append(f"abbrev tree : BankAudit := {root_name}\n")
        parts.append(f"theorem checked : bankCheck bank B {pexpr} tree = true := {root_name}_checked\n")
        parts.append(
            f"theorem residual_count : (bankResiduals {pexpr} tree).length = {rn} := by decide +kernel\n"
        )
        parts.append(f"#print axioms checked\n#print axioms residual_count\nend {bns}\n")
        (out / f"{mod}.lean").write_text("".join(parts))
        branch_names.append(f"{NS}.Branch{i:02d}.tree")

    assert seen == opens, (len(seen), len(opens))
    assert len(opens) == 671, len(opens)
    masses = []
    for code in opens:
        holes = code.replace("_", "").count("---")
        masses.append(25 ** holes)
    assert sum(masses) == 24575, sum(masses)

    imports = "".join(f"import Raw54OneRDBranch{i:02d}\n" for i in range(24))
    kids_expr = ",".join(branch_names)
    root = f"""{imports}
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {NS}
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10FastAudit

def kids : Move → BankAudit := byBankMove [{kids_expr}]
def tree : BankAudit := .split {n} {slot(s)} kids

theorem kids_checked (z : Move) :
    bankCheck bank B (refine parent {slot(s)} (some z)) (kids z) = true := by
  rcases z with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
"""
    for q in range(6):
        for w, r in [(0, 0), (0, 1), (1, 0), (1, 1)]:
            i = 12 * w + 6 * r + q
            root += f"  · exact Branch{i:02d}.checked\n"
    root += f"""
theorem checked : bankCheck bank B parent tree = true := by
  change (queryOK B parent {n} {slot(s)} &&
    allMoves (fun z => bankCheck bank B (refine parent {slot(s)} (some z)) (kids z))) = true
  simp only [Bool.and_eq_true]
  exact ⟨by decide +kernel,allMoves_of _ kids_checked⟩

def residuals := bankResiduals parent tree

theorem residual_count : residuals.length = {len(opens)} := by decide +kernel

theorem cut (m : Machine) (hm : compatible parent m) :
    WeightedBound B m ∨ ∃ e ∈ residuals, compatible e.2 m :=
  bankSound bank B parent tree parent_root parent_nohalt checked m hm

theorem close
    (hres : ∀ e ∈ residuals, Cover (WeightedBound B) e.2) :
    Cover (WeightedBound B) parent :=
  bankClose bank B parent tree parent_root parent_nohalt checked hres

#print axioms checked
#print axioms residual_count
#print axioms cut
#print axioms close
end {NS}
"""
    (out / "Raw54OneRDBankCut.lean").write_text(root)
    branch_summary = []
    for i, child in enumerate(kids):
        bp = refine(parent, s, i)
        rn, rm = residual_stats(child, bp)
        branch_summary.append({
            "move_code": i, "move": move(i), "tree_nodes": tree_size(child),
            "residual_nodes": rn, "residual_mass": rm,
        })
    assert sum(x["residual_nodes"] for x in branch_summary) == len(opens)
    assert sum(x["residual_mass"] for x in branch_summary) == sum(masses)

    (discovery / "generator-summary.json").write_text(json.dumps({
        "bank": len(bank), "residual_nodes": len(opens),
        "residual_mass": sum(masses), "bound": BOUND,
        "root_query": [n, s], "tree_nodes": tree_size(tree),
        "branches": branch_summary,
    }, indent=2) + "\n")
    print("generated compact 1RD replay:",
          "bank", len(bank), "residuals", len(opens),
          "mass", sum(masses), "tree_nodes", tree_size(tree),
          "root_query", n, s)


if __name__ == "__main__":
    main()
