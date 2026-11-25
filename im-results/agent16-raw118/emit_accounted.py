"""Emit local, source-checked Raw118 cover grafts instead of a global residual reduction."""
from itertools import product
from pathlib import Path
import json
import re


def emit(here, work, rows, entries, table_key, literal_table, emit_tree):
    from generate_partial import MOVES, move, slot, size, CASES
    here, work = Path(here), Path(work)
    holdout_index = 2869
    residual = {rows[i]: i for i in set(entries) | {holdout_index}}
    assert len(residual) == len(entries) + 1
    assert len(entries) == 958
    sparse = json.loads((here / "Raw118Sparse.json").read_text())
    symbolic = json.loads((here / "Raw118Symbolic.json").read_text())
    modules = {}
    for root in sparse["modules"]:
        source = (here / f"{root}.lean").read_text()
        for i in set(map(int, re.findall(
                r"^namespace BB6\.Agent47SparseNGram\.Raw118Sparse(\d+)$", source, re.M))):
            assert i not in modules
            modules[i] = root
    assert set(modules) == set(sparse["indices"])
    for claim in symbolic["claims"]:
        i = int(claim["index"])
        assert i not in modules
        modules[i] = claim["namespace"].split(".")[-2]
    fixed = {
        "Agent40Independent.Raw118.": "Raw118Independent",
        "Agent40PhaseGraph.Raw118.": "Raw118PhaseGraph",
        "Agent40Recursive.Raw118.": "Raw118Recursive",
        "Agent40Recursive.Raw118More.": "Raw118RecursiveMore",
        "Agent16BiDFA.Raw118.M": "Raw118BiDFA",
        "Agent16BiDFA.Raw118Tree.M": "Raw118Tree",
        "Agent16BiDFA.Raw118TreeBank.M": "Raw118TreeBank",
        "Agent1BiDFASat.Raw118.M": "Raw118SatHits",
        "Agent40Raw118CrossBank.": "Raw118SatCrossBank",
        "Agent1Raw118M3981.": "Raw118M3981",
        "Agent1Raw118Radix4.": "Raw118Radix4",
    }
    numbered = {
        "Agent1BiDFAWide.M": "Raw118Wide",
        "Agent40Raw118Run.M": "Raw118Run",
        "Agent16Raw118Nested.M": "Raw118Nested",
        "Agent16Raw118Late.M": "Raw118Late",
    }
    for i, proof in entries.items():
        if i in modules:
            continue
        matches = [name for prefix, name in fixed.items() if prefix in proof]
        matches += [name + str(i) for prefix, name in numbered.items() if prefix in proof]
        assert len(matches) == 1, (i, proof, matches)
        modules[i] = matches[0]
    assert set(modules) == set(entries)

    header = """set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent16Raw118Consumer
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent16Raw118 BB6.Agent16ResidualCover
open BB6.Agent8TNFPath BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
"""
    def write(name, deps, body):
        (here / (name + ".lean")).write_text(
            "".join(f"import {dep}\n" for dep in dict.fromkeys(deps))
            + header + body + "\nend BB6.Agent16Raw118Consumer\n")

    write("Raw118Holdout", ["Raw118Base", "ResidualAccounted"],
          "def holdout : PartialMachine := " + literal_table(rows[holdout_index]))
    seen = set()
    plan = []
    def leaves(t):
        if t[0] == "open":
            i = residual.get(t[1])
            if i is not None:
                yield i
        elif t[0] == "split":
            for child in t[3]:
                yield from leaves(child)

    def go(t, p, path):
        name = "Raw118Close" + path
        theorem = "closed" + path
        if size(t) <= 1200:
            ids = list(leaves(t))
            assert len(ids) == len(set(ids)) and not (seen & set(ids)), (path, ids)
            seen.update(ids)
            keys = sorted((table_key(rows[i]), entries[i]) for i in ids if i != holdout_index)
            tree = emit_tree(keys)
            deps = ["Raw118Holdout", "Raw118Node" + path]
            deps += sorted({modules[i] for i in ids if i != holdout_index})
            write(name, deps, f"""
def certificates{path} : AcceptedTree bound := {tree}
theorem accounted{path} : accountedCheck certificates{path} holdout ({p}) audit{path} = true := by decide
theorem {theorem} : ConditionalCover bound ({p}) holdout :=
  leafConditional holdout ({p}) audit{path} certificates{path} audit{path}_checked accounted{path}
""")
            plan.append({"module": name, "indices": sorted(ids), "imports": deps})
        else:
            assert t[0] == "split"
            _, n, s, kids = t
            parts = [go(k, f"refine ({p}) {slot(s)} (some {move(MOVES[j])})", path + f"_{j:02}")
                     for j, k in enumerate(kids)]
            cases = "\n".join("  · exact " + parts[12*w+6*r+q][1]
                              for q,w,r in product(range(6),range(2),range(2)))
            write(name, ["Raw118Holdout", *(x[0] for x in parts)], f"""
theorem {theorem} : ConditionalCover bound ({p}) holdout := by
  apply splitConditional holdout ({p}) {n} {slot(s)} (by decide)
  intro mv
{CASES}{cases}
""")
        return name, theorem
    t = json.loads((work / "tree.json").read_text())
    assert t[:3] == ["split", 9, 8]
    root, theorem = go(t, "parent", "Root")
    assert seen == set(entries) | {holdout_index}, (set(entries) | {holdout_index}) - seen
    write("Raw118Consumer", [root, "Raw118Sharp"], f"""
/-- Every compatible completion is bounded or lies in the exact holdout. -/
theorem sound_after : ∀ m, compatible parent m → WeightedBound bound m ∨ compatible holdout m :=
  {theorem} parent_root parent_nohalt

/-- Stable local contract; the holdout is an explicit, separate premise. -/
theorem parent_cover_at_target {{B : Nat}} (hB : bound ≤ B)
    (h : Cover (WeightedBound B) holdout) : Cover (WeightedBound B) parent := by
  refine Cover.leaf _ ?_
  intro m hm
  rcases sound_after m hm with hb | hc
  · intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) hB
  · exact h.sound m hc

theorem parent_exact_if_holdout (h : Cover (WeightedBound bound) holdout) :
    Cover (WeightedBound bound) parent ∧ ∀ B, Cover (WeightedBound B) parent → bound ≤ B :=
  ⟨parent_cover_at_target (Nat.le_refl _) h, fun _ hB => BB6.Agent16Raw118.parent_min_weighted_bound hB⟩

#print axioms sound_after
#print axioms parent_cover_at_target
#print axioms parent_exact_if_holdout
""")
    result = {"mode": "subtree-accounted", "leaf_shards": plan,
              "candidate_total": len(entries), "holdout_index": holdout_index}
    (here / "Raw118AccountedPlan.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"Raw118 accounted {len(seen)} residuals over {len(plan)} local audit shards")
    return result
