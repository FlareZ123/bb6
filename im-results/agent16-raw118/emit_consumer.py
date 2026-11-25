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
    remaining_hard = sorted(remaining_before_treebank - treebank_ids)
    assert len(remaining_hard) == 87 - len(treebank_ids), len(remaining_hard)
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

    entries = []
    def add_nonhalt(ns: str):
        entries.append(
            "  BB6.Agent16ResidualCover.nonhalt bound "
            f"{ns}.table (fun m hm => {ns}.never m hm)"
        )

    for i in sorted(independent):
        add_nonhalt(f"BB6Coverage.Agent40Independent.Raw118.M{i}")
    for i in sorted(phase):
        add_nonhalt(f"BB6Coverage.Agent40PhaseGraph.Raw118.M{i}")
    for i in sorted(int(x[0]) for x in RECURSIVE_CASES):
        add_nonhalt(f"BB6Coverage.Agent40Recursive.Raw118.M{i}")
    for i in sorted(int(x[0]) for x in RECURSIVE_MORE_CASES):
        add_nonhalt(f"BB6Coverage.Agent40Recursive.Raw118More.M{i}")
    for i in sorted(bidfa):
        add_nonhalt(f"BB6Coverage.Agent16BiDFA.Raw118.M{i}")
    for i in sorted(tree):
        add_nonhalt(f"BB6Coverage.Agent16BiDFA.Raw118Tree.M{i}")
    for claim in sorted(symbolic, key=lambda x: int(x["index"])):
        add_nonhalt(claim["namespace"])
    for claim in sorted(sparse, key=lambda x: int(x["index"])):
        add_nonhalt(claim["namespace"])
    for hit in sorted(treebank, key=lambda x: int(x["index"])):
        add_nonhalt(f"BB6Coverage.Agent16BiDFA.Raw118TreeBank.M{int(hit['index'])}")
    for leaf in sorted(late, key=lambda x: int(x["index"])):
        ns = f"BB6.Agent16Raw118Late.M{int(leaf['index'])}"
        entries.append(
            f"  ⟨{ns}.table, {ns}.longCertificate.sound⟩"
        )

    imports = [
        "Raw118Partial",
        "ResidualCover",
        "Raw118Symbolic",
        "Raw118Sparse",
        "Raw118Independent",
        "Raw118PhaseGraph",
        "Raw118Recursive",
        "Raw118RecursiveMore",
        "Raw118BiDFA",
        "Raw118Tree",
        "Raw118Late",
        "Raw118TreeBank",
    ]
    header = "\n".join(f"import {name}" for name in imports)
    source = f'''{header}

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent16Raw118Consumer

open BB6Coverage BB6.Agent16Raw118 BB6.Agent16ResidualCover

def accepted : List (Accepted bound) := [
{",\n".join(entries)}
]

def remaining := BB6.Agent16ResidualCover.remaining accepted residuals

theorem accepted_count : accepted.length = {872 + len(treebank_ids)} := by rfl

/-- The Raw118 parent is covered at 756496 except for this exact finite
    complement of one-hole residual tables. -/
theorem sound_after :
    ∀ m, compatible parent m → WeightedBound bound m ∨
      ∃ e ∈ remaining, compatible e.2 m :=
  BB6.Agent16ResidualCover.consume accepted sound

theorem remaining_count : remaining.length = {len(remaining_hard)} := by decide

def holeCount (p : PartialMachine) : Nat :=
  (List.finRange 6).foldl (fun n q =>
    n + (if p (q,false) = none then 1 else 0) +
        (if p (q,true) = none then 1 else 0)) 0

theorem remaining_one_hole :
    remaining.all (fun e => decide (holeCount e.2 = 1)) = true := by decide

#print axioms sound_after
#print axioms remaining_count
#print axioms remaining_one_hole

end BB6.Agent16Raw118Consumer
'''
    (HERE / "Raw118Consumer.lean").write_text(source)
    manifest = {
        "open_rows": len(rows),
        "hard_rows": len(hard),
        "hard_accepted": len(hard_accepted),
        "hard_residuals": remaining_hard,
        "ngram_accepted": len(sparse_ids),
        "late_accepted": len(late_ids),
        "treebank_accepted": len(treebank_ids),
        "treebank_indices": sorted(treebank_ids),
        "accepted_total": len(hard_accepted | sparse_ids | late_ids | treebank_ids),
        "expected_parent_residuals": len(remaining_hard),
        "imports": imports,
    }
    (HERE / "Raw118Consumer.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print("Raw118 parent consumer:", manifest)


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: emit_consumer.py WORKDIR")
    main(Path(sys.argv[1]))
