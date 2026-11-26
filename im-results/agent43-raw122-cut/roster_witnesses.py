#!/usr/bin/env python3
"""Generate exact Lean witness maps for Raw122 residual rosters.

Every roster table is matched by its complete 36-character transition string
against a kernel-checkable indexed witness, a direct recurrent witness, or an
explicit special bounded-run theorem. Any unmatched table is a hard error.
"""
from __future__ import annotations
from pathlib import Path
import json
import sys

def load_hits(path: Path):
    out = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        c = line.split()
        if len(c) < 3:
            continue
        idx, shard, table = int(c[0]), c[1], c[2]
        if table in out and out[table][0] != idx:
            raise RuntimeError(f"duplicate indexed witness table: {table}")
        out[table] = (idx, shard)
    return out

def load_direct(path: Path):
    out = {}
    for row in json.loads(path.read_text(encoding="utf-8")):
        table = row["table"].replace("_", "")
        out[table] = int(row["id"])
    return out

def eq_lines(lhs: str, rhs: str):
    return [
        f"  · have he : {lhs} = {rhs} := by",
        "      funext s",
        "      rcases s with ⟨q,b⟩",
        "      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega",
        "      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl",
    ]

def build(branch: int, roster_tsv: Path, hits_tsv: Path,
          direct_json: Path, output: Path):
    tag = f"{branch:02}"
    hits = load_hits(hits_tsv)
    direct = load_direct(direct_json)
    rows = []
    for line in roster_tsv.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        ident, table = line.split("\t")
        rows.append((ident, table))
    if not rows:
        raise RuntimeError(f"branch {tag} has no residual tables; use the closed-branch path")

    selected_hits = set()
    selected_direct = set()
    selected_specials = []
    proofs = []
    for ident, table in rows:
        lhs = ident
        if table in hits:
            idx, shard = hits[table]
            if not shard.startswith(f"Raw122Kid{tag}_"):
                raise RuntimeError(f"wrong source shard for {ident}: {shard}")
            selected_hits.add(idx)
            rhs = f"BB6Coverage.Agent29Raw122Indexed.M{idx:03}.table"
            proofs.append(("never", lhs, rhs,
                           f"BB6Coverage.Agent29Raw122Indexed.M{idx:03}.never"))
        elif table in direct:
            idx = direct[table]
            selected_direct.add(idx)
            rhs = f"BB6Coverage.Agent31Pump.Raw122DirectGrowth.M{idx}.table"
            proofs.append(("never", lhs, rhs,
                           f"BB6Coverage.Agent31Pump.Raw122DirectGrowth.M{idx}.never"))
        elif branch == 16 and ident == "p16_012":
            selected_specials.append("late1")
            rhs = "BB6Coverage.Agent29PackedLate.M1.table"
            proofs.append(("late", lhs, rhs,
                           "BB6Coverage.Agent29PackedLate.M1.bound"))
        elif branch == 17 and ident == "p17_022":
            selected_specials.append("counter17")
            rhs = "BB6Coverage.Agent43Raw122Counter17.table"
            proofs.append(("never", lhs, rhs,
                           "BB6Coverage.Agent43Raw122Counter17.never"))
        else:
            raise RuntimeError(f"no checked witness mapping for {ident}: {table}")

    imports = [f"Raw122Roster{tag}"]
    imports += [f"Agent29Raw122Indexed{i:03}" for i in sorted(selected_hits)]
    imports += [f"Raw122Direct{i}" for i in sorted(selected_direct)]
    if "late1" in selected_specials:
        imports.append("LateCheck1")
    if "counter17" in selected_specials:
        imports.append("Raw122Counter17")

    lines = [f"import {x}" for x in imports]
    lines += [
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 0",
        "namespace BB6.Agent43Raw122Roster",
        "open BB6Coverage BB6.Agent43Raw122ResidualCompose",
        f"theorem witnesses{tag} : ∀ p ∈ tables{tag}, Covered 6766859 p := by",
        "  intro p hp",
        f"  simp only [tables{tag},List.mem_cons,List.not_mem_nil,or_false] at hp",
        "  rcases hp with " + "|".join("rfl" for _ in rows),
    ]
    for kind, lhs, rhs, theorem in proofs:
        lines += eq_lines(lhs, rhs)
        if kind == "late":
            lines += [
                "    intro m hm",
                f"    have hm' : compatible {rhs} m := by",
                "      rw [← he]",
                "      exact hm",
                f"    exact {theorem} m hm'",
            ]
        else:
            lines += [
                "    rw [he]",
                f"    exact never_bound ({theorem})",
            ]
    lines += [
        f"#print axioms witnesses{tag}",
        "end BB6.Agent43Raw122Roster",
        "",
    ]
    output.write_text("\n".join(lines), encoding="utf-8")
    return {
        "branch": branch,
        "residual_count": len(rows),
        "indexed_ids": sorted(selected_hits),
        "direct_ids": sorted(selected_direct),
        "specials": selected_specials,
        "witness_module": output.name,
    }

if __name__ == "__main__":
    if len(sys.argv) != 6:
        raise SystemExit("usage: roster_witnesses.py BRANCH ROSTER.tsv hits.tsv direct_certificates.json OUTPUT.lean")
    result = build(int(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3]),
                   Path(sys.argv[4]), Path(sys.argv[5]))
    print(json.dumps(result, sort_keys=True), flush=True)
