#!/usr/bin/env python3
"""Assemble the source-checked Raw118 certificates into an exact parent residual cover."""
from pathlib import Path
import json
import sys

HERE = Path(__file__).resolve().parent
IM = HERE.parent
AG40 = IM / "agent40-raw118-independent"
sys.path.insert(0, str(AG40))

from independent import ROWS as INDEPENDENT_ROWS
from generate_recursive_counter import CASES as RECURSIVE_CASES
from generate_recursive_more import CASES as RECURSIVE_MORE_CASES
from bidfa_emit import EXAMPLES as BIDFA_EXAMPLES
from tree_emit import EXAMPLES as TREE_EXAMPLES


def main(work: Path) -> None:
    rows = (work / "open.txt").read_text().splitlines()
    candidates = json.loads((work / "candidates.json").read_text())
    hard = {int(i) for i in candidates["hard"]}
    ngram = {int(i) for i in candidates["ngram"]}
    symbolic = json.loads((HERE / "Raw118Symbolic.json").read_text())["claims"]
    sparse = json.loads((HERE / "Raw118Sparse.json").read_text())["claims"]
    late = json.loads((HERE / "Raw118Late.json").read_text())["leaves"]
    treebank_manifest = json.loads((HERE / "Raw118TreeBank.json").read_text())
    treebank = treebank_manifest["emitted"]
    treebank_ids = {int(x["index"]) for x in treebank}
    sat_hits = json.loads((IM / "agent1-bidfa-sat" / "raw118-sat-hits.json").read_text())
    sat_by_id = {int(x["index"]): x for x in sat_hits}
    assert len(sat_by_id) == len(sat_hits)
    for i, hit in sat_by_id.items():
        assert 0 <= i < len(rows) and hit["table"] == rows[i], (i, hit["table"], rows[i])
    sat_ids = set(sat_by_id)
    wide_widths = json.loads((IM / "agent1-bidfa-sat" / "raw118-wide-widths.json").read_text())
    wide_ids = {int(i) for i in wide_widths}
    phase = {
        int(line.split()[0])
        for line in (AG40 / "phase_candidates.tsv").read_text().splitlines()
        if line.strip()
    }
    independent = set(INDEPENDENT_ROWS)
    recursive = {int(x[0]) for x in RECURSIVE_CASES + RECURSIVE_MORE_CASES}
    bidfa = {int(x[0]) for x in BIDFA_EXAMPLES}
    tree = {int(x[0]) for x in TREE_EXAMPLES}
    symbolic_ids = {int(x["index"]) for x in symbolic}
    sparse_ids = {int(x["index"]) for x in sparse}
    late_ids = {int(x["index"]) for x in late}

    hard_groups = {
        "symbolic": symbolic_ids,
        "independent": independent,
        "phasegraph": phase,
        "recursive": recursive,
        "bidfa": bidfa,
        "tree": tree,
    }
    names = list(hard_groups)
    for i, a in enumerate(names):
        for b in names[i + 1:]:
            overlap = hard_groups[a] & hard_groups[b]
            assert not overlap, (a, b, sorted(overlap))
    hard_accepted = set().union(*hard_groups.values())
    assert len(hard) == 274
    assert len(hard_accepted) == 187, len(hard_accepted)
    assert hard_accepted <= hard
    remaining_before_treebank = hard - hard_accepted
    assert treebank_ids <= remaining_before_treebank
    assert len(treebank_ids) == len(treebank)
    assert sat_ids <= remaining_before_treebank
    sat_new_ids = sat_ids - treebank_ids
    assert not (sat_new_ids & hard_accepted)
    assert not (sat_new_ids & treebank_ids)
    assert len(sat_ids) == 11
    assert sat_ids & treebank_ids == {2873}
    assert len(wide_ids) == 47
    assert wide_ids <= remaining_before_treebank
    assert not (wide_ids & sat_ids)
    assert not (wide_ids & treebank_ids)
    assert not (wide_ids & hard_accepted)
    remaining_hard = sorted(remaining_before_treebank - treebank_ids - sat_new_ids - wide_ids)
    assert len(remaining_hard) == 87 - len(treebank_ids) - len(sat_new_ids) - len(wide_ids), len(remaining_hard)
    assert all(rows[i].count("---") == 1 for i in remaining_hard)

    assert len(symbolic) == 105
    assert len(sparse) == 679
    assert len(late) == 6
    assert sparse_ids == ngram
    assert not (sparse_ids & hard)
    assert not (late_ids & (sparse_ids | hard))
    assert len(rows) == 6085
    assert len(sparse_ids | hard | late_ids) == 959
    assert len(hard_accepted | sparse_ids | late_ids | treebank_ids) == 872 + len(treebank_ids)

    # Prefer the compact macro proofs for 4188/4197 to their much larger
    # second-order run-summary certificates. The other 20 run-summary rows
    # have successful focused source audits.
    run_ids = {430,437,440,456,1181,3908,1120,1127,1174,1326,1390,1391,
               1392,1816,2867,3921,4093,4125,4342,4443}
    run_manifest = json.loads((AG40 / "run-generated" / "manifest.json").read_text())
    assert {int(x["index"]) for x in run_manifest} == run_ids
    assert all(rows[int(x["index"])] == x["table"] for x in run_manifest)
    nested_ids = {10,434,655,657}
    extra_groups = [run_ids, nested_ids, {3970}, {3981,4188,4197}]
    extra_ids = set().union(*extra_groups)
    assert sum(map(len, extra_groups)) == len(extra_ids) == 28
    assert extra_ids <= set(remaining_hard)
    remaining_hard = sorted(set(remaining_hard) - extra_ids)
    assert remaining_hard == [2869], remaining_hard
    assert rows[2869] == "1RB0LB_1RC0RA_0RD0RF_1LD1RE_1LB0LE_1RA---"

    entries = {}
    def add(i, proof):
        assert i not in entries, i
        entries[i] = proof

    def add_nonhalt(i, ns, args=""):
        add(i, "BB6.Agent16ResidualCover.nonhalt bound "
            f"({ns}.table{args}) (fun m hm => {ns}.never{args} m hm)")

    for i in sorted(independent):
        add_nonhalt(i, f"BB6Coverage.Agent40Independent.Raw118.M{i}")
    for i in sorted(phase):
        add_nonhalt(i, f"BB6Coverage.Agent40PhaseGraph.Raw118.M{i}")
    for i in sorted(int(x[0]) for x in RECURSIVE_CASES):
        add_nonhalt(i, f"BB6Coverage.Agent40Recursive.Raw118.M{i}")
    for i in sorted(int(x[0]) for x in RECURSIVE_MORE_CASES):
        add_nonhalt(i, f"BB6Coverage.Agent40Recursive.Raw118More.M{i}")
    for i in sorted(bidfa):
        add_nonhalt(i, f"BB6Coverage.Agent16BiDFA.Raw118.M{i}")
    for i in sorted(tree):
        add_nonhalt(i, f"BB6Coverage.Agent16BiDFA.Raw118Tree.M{i}")
    for claim in symbolic + sparse:
        add_nonhalt(int(claim["index"]), claim["namespace"])
    for hit in treebank:
        i = int(hit["index"])
        add_nonhalt(i, f"BB6Coverage.Agent16BiDFA.Raw118TreeBank.M{i}")
    for i in sorted(sat_new_ids):
        add_nonhalt(i, f"BB6Coverage.Agent1BiDFASat.Raw118.M{i}")
    for i in sorted(wide_ids):
        add_nonhalt(i, f"BB6Coverage.Agent1BiDFAWide.M{i}")
    for leaf in late:
        i = int(leaf["index"])
        ns = f"BB6.Agent16Raw118Late.M{i}"
        add(i, f"⟨{ns}.table, {ns}.longCertificate.sound⟩")
    for i in sorted(run_ids):
        add_nonhalt(i, f"BB6Coverage.Agent40Raw118Run.M{i}")
    for i in sorted(nested_ids):
        add_nonhalt(i, f"BB6Coverage.Agent16Raw118Nested.M{i}")
    add_nonhalt(3970, "BB6Coverage.Agent40Raw118CrossBank.M3970")
    add_nonhalt(3981, "BB6Coverage.Agent1Raw118M3981")
    add_nonhalt(4188, "BB6Coverage.Agent1Raw118Radix4", " false")
    add_nonhalt(4197, "BB6Coverage.Agent1Raw118Radix4", " true")

    assert set(entries) == (sparse_ids | hard | late_ids) - {2869}
    assert len(entries) == 958

    def table_key(row):
        raw = row.replace("_", "")
        assert len(raw) == 36
        key = 0
        for j in range(0,36,3):
            mv = raw[j:j+3]
            digit = 0 if mv == "---" else 2 + 12*int(mv[0]) + 6*(mv[1]=="R") + ord(mv[2])-65
            key = key*26 + digit
        return key

    def literal_table(row):
        raw = row.replace("_","")
        lines = ["fun s => match s.1.val, s.2 with"]
        for j in range(12):
            mv = raw[3*j:3*j+3]
            if mv != "---":
                lines.append(f"  | {j//2}, {str(bool(j%2)).lower()} => some (some ⟨{str(mv[0]=='1').lower()}, {str(mv[1]=='R').lower()}, {ord(mv[2])-65}⟩)")
        lines.append("  | _, _ => none")
        return "\n".join(lines)

    keyed = sorted((table_key(rows[i]), proof) for i,proof in entries.items())
    assert len({key for key,_ in keyed}) == len(keyed)

    def emit_tree(items):
        if not items:
            return ".empty"
        mid = len(items)//2
        key, proof = items[mid]
        return f"(.node {key} ({proof}) {emit_tree(items[:mid])} {emit_tree(items[mid+1:])})"

    imports = [
        "Raw118Partial", "ResidualKeyed", "Raw118Symbolic", "Raw118Sparse",
        "Raw118Independent", "Raw118PhaseGraph", "Raw118Recursive",
        "Raw118RecursiveMore", "Raw118BiDFA", "Raw118Tree", "Raw118Late",
        "Raw118TreeBank", "Raw118SatHits", "Raw118SatCrossBank",
        "Raw118M3981", "Raw118Radix4",
    ]
    imports.extend(f"Raw118Wide{i}" for i in sorted(wide_ids))
    imports.extend(f"Raw118Run{i}" for i in sorted(run_ids))
    imports.extend(f"Raw118Nested{i}" for i in sorted(nested_ids))
    header = "\n".join(f"import {name}" for name in imports)
    entries_text = emit_tree(keyed)
    holdout_text = literal_table(rows[2869])
    source = f'''{header}

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent16Raw118Consumer
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent16Raw118 BB6.Agent16ResidualCover

def accepted : AcceptedTree bound := {entries_text}
def remaining := remainingTree accepted residuals
def holdout : PartialMachine := {holdout_text}

theorem accepted_count : accepted.size = {len(entries)} := by rfl

/-- Exact source-cover dichotomy; no finite simulation assumption. -/
theorem sound_after :
    ∀ m, compatible parent m → WeightedBound bound m ∨
      ∃ e ∈ remaining, compatible e.2 m :=
  consumeTree accepted sound

theorem remaining_count : remaining.length = 1 := by decide

/-- The table, not just the number of residuals, must match the holdout. -/
theorem remaining_exact :
    remaining.all (fun e => sameTable e.2 holdout) = true := by decide

/-- Stable score-parametric local contract. The only remaining cylinder is
    an explicit premise; this does not presume a verdict for row 2869. -/
theorem parent_cover_at_target {{B : Nat}} (hB : bound ≤ B)
    (h : Cover (WeightedBound B) holdout) : Cover (WeightedBound B) parent := by
  refine Cover.leaf _ ?_
  intro m hm
  rcases sound_after m hm with hb | ⟨e,he,hc⟩
  · intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) hB
  · have heq := sameTable_sound (List.all_eq_true.mp remaining_exact e he)
    exact h.sound m (heq ▸ hc)

#print axioms sound_after
#print axioms remaining_count
#print axioms remaining_exact
#print axioms parent_cover_at_target

end BB6.Agent16Raw118Consumer
'''
    (HERE / "Raw118Consumer.lean").write_text(source)
    manifest = {
        "open_rows":len(rows), "hard_rows":len(hard),
        "hard_base_accepted":len(hard_accepted),
        "hard_candidate_covered":len(hard)-1,
        "hard_residuals":remaining_hard,
        "holdout_table":rows[2869],
        "ngram_candidate_count":len(sparse_ids),
        "late_candidate_count":len(late_ids),
        "treebank_indices":sorted(treebank_ids),
        "sat_new_indices":sorted(sat_new_ids),
        "wide_indices":sorted(wide_ids),
        "extra_indices":sorted(extra_ids),
        "candidate_total":len(entries),
        "expected_parent_residuals":len(remaining_hard),
        "imports":imports,
    }
    (HERE / "Raw118Consumer.json").write_text(json.dumps(manifest,indent=2)+"\n")
    print("Raw118 parent consumer:",manifest)


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: emit_consumer.py WORKDIR")
    main(Path(sys.argv[1]))
