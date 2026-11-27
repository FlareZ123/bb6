#!/usr/bin/env python3
"""Consume the existing exact early-cylinder theorems in the full Raw42 tree.

The discovery tree is untrusted. Every replacement is an Audit.proven of
the actual seven-transition refinement, so PackedAudit checks table identity
and Lean checks the universal nonhalting proof. No skipped discovery node
is silently taken as nonhalting. TNF-disallowed labels remain .keep.
"""
import re
from pathlib import Path

def install(raw, out, branch, tree, ids, late_splits):
    code = 12 * int(branch[0]) + 6 * (branch[1] == "R") + ord(branch[2]) - 65
    source = (raw / "Raw42EarlyNGram.lean").read_text()
    match = re.search(
        rf"^def cut{code} : Cut := ⟨{code},(\d+),(\d+),\[\n(.*?)\n\],\[(.*?)\]⟩$",
        source, re.M | re.S)
    if match is None:
        return {}, set(), set(), {}
    time, slot, rows, extra = match.groups()
    assert tree[0] == "split" and tree[1:3] == [int(time), int(slot)]
    entries = [int(x) for x in re.findall(r"^\s*⟨(\d+),", rows, re.M)]
    assert entries and len(entries) == len(set(entries))
    extras = [int(x) for x in extra.split(",") if x.strip()]
    growth = {
        (0,20): ("Wide", "ZeroLAOneRC"),
        (12,9): ("Wide", "OneLAZeroRD"),
        (13,3): ("Nested", "OneLBZeroLD"),
        (13,9): ("Nested", "OneLBZeroRD"),
        (13,20): ("Wide", "OneLBOneRC"),
        (14,7): ("Wide", "OneLCZeroRB"),
        (14,9): ("Wide", "OneLCZeroRD"),
        (14,14): ("Nested", "OneLCOneLC"),
        (19,8): ("Wide", "OneRBZeroRC"),
        (19,14): ("Wide", "OneRBOneLC"),
        (22,15): ("Wide", "OneREOneLD"),
    }
    assert set(entries).isdisjoint(extras)
    mod = f"Raw42{branch}EarlyPrune"
    ns = f"BB6.Agent32Raw42{branch}.EarlyPrune"
    declarations = [
        "import Raw42EarlyNGram",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 0",
        f"namespace {ns}",
        "open BB6Coverage BB6.Agent32Raw42Early",
    ]
    proofs = {}
    removed, removed_extra = set(), set()
    stats = {}

    def count(t):
        tag = t[0]
        if tag == "split":
            return 1 + sum(count(k) for k in t[3])
        if tag == "open":
            j = ids[t[1]]
            assert j not in removed
            removed.add(j)
            if j in late_splits:
                for child in late_splits[j][3]:
                    if child[0] == "open":
                        assert child[2] not in removed_extra
                        removed_extra.add(child[2])
        return 1

    for i, move in enumerate(entries):
        old = tree[3][move]
        if old[0] not in ("split", "open"):
            continue
        stats[str(move)] = count(old)
        tree[3][move] = ["early", move]
        declarations.extend([
            f"abbrev p{move} : PartialMachine := sub cut{code} {move}",
            f"def cert{move} := (cut{code}.rows[{i}]).cert",
            f"theorem live{move} : ∀ m, compatible p{move} m → NeverHalts m :=",
            f"  BB6.Agent32AsymNGram.never p{move} cert{move} (by decide)",
            f"#print axioms live{move}",
        ])
        proofs[move] = (f".proven {ns}.p{move} {ns}.live{move}", mod)
    for move in extras:
        old = tree[3][move]
        if old[0] not in ("split", "open"):
            continue
        group, name = growth[(code, move)]
        stats[str(move)] = count(old)
        tree[3][move] = ["early", move]
        base = f"BB6.Agent32Raw42{group}.{name}"
        proofs[move] = (f".proven {base}.p {base}.never", f"Raw42{group}Growth")
    declarations.append(f"end {ns}")
    if any(module == mod for _, module in proofs.values()):
        (out / (mod + ".lean")).write_text("\n".join(declarations) + "\n")
    return proofs, removed, removed_extra, stats
