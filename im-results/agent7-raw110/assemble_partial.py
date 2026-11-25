"""Assemble the *entire* raw110 parent from the sixteen separately checked
ordinary child audits and eight exact immediate-cycle leaves.

This script emits only Lean expressions and proof terms. It does not
trust the candidate roster, count, classifier or witness generator.
"""
from pathlib import Path
import json, sys
from block_overlay import partial_spec
from itertools import product

ROOT = Path(__file__).resolve().parent
full = json.loads((ROOT / "spec.json").read_text())
partial = partial_spec("--block-far" in sys.argv)
assert not set(full) & set(partial)
cycles = {2:(10,1,False,0),4:(10,1,False,0),7:(1,9,True,1),9:(13,1,False,1),
          15:(11,1,False,-1),16:(10,1,False,0),19:(1,9,True,1),21:(4,4,True,1)}
assert set(map(int, full)) | set(map(int, partial)) | set(cycles) == set(range(24))
assert not (set(map(int, full)) | set(map(int, partial))) & set(cycles)

kids, checks, counts, count_checks, imports = [], [], [], [], []
for i in range(24):
    if i in cycles:
        e,k,r,b=cycles[i]
        kids.append(f".closed (.cycle {e} {k} {str(r).lower()} ({b}))")
        checks.append("  · decide")
        counts.append(0)
        count_checks.append("  · rfl")
    else:
        imports.append(f"Raw110Partial{i:02}")
        assert (ROOT/f"Raw110Partial{i:02}.lean").is_file(), i
        kids.append(f"partialKid{i:02}")
        checks.append(f"  · exact partialKid{i:02}_checked")
        counts.append(len(partial[str(i)]["miss"]) if str(i) in partial else 0)
        count_checks.append(f"  · exact countPartial{i:02}")

def ordered(lines):
    return "\n".join(lines[12*w+6*r+q] for q,w,r in product(range(6),range(2),range(2)))

cases = """  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
"""
body = "".join(f"import {m}\n" for m in ["Raw110Consumer", *imports])
body += """set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw110
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole
open BB6.Agent10ZipAudit BB6.Agent47PartialAudit

def assembledKids : Move → PartialAudit := byPartialMove [
"""
body += ",\n".join(kids) + "]\n"
body += """theorem assembledKids_checked (mv : Move) :
    partialCheck 7014 (child110 mv) (assembledKids mv) = true := by
""" + cases + ordered(checks) + "\n"
body += "def expectedCount (mv : Move) : Nat :=\n  ([" + ",".join(map(str,counts)) + "] : List Nat)[12*mv.write.toNat+6*mv.right.toNat+mv.next.val]?.getD 0\n"
body += """theorem assembledKids_count (mv : Move) :
    (partialResiduals (child110 mv) (assembledKids mv)).length = expectedCount mv := by
""" + cases + ordered(count_checks) + "\n"
body += f"""
/-- Derive the global descendant count from the independently checked
    child counts, rather than reducing all the closed certificate data. -/
theorem assembledResidual_count : (deepResiduals assembledKids).length = {sum(counts)} := by
  change (auditMoves.flatMap fun mv =>
    (partialResiduals (child110 mv) (assembledKids mv)).map
      (fun e => (mv :: e.1,e.2))).length = _
  rw [List.length_flatMap]
  simp only [List.length_map]
  rw [List.map_congr_left (fun mv _ => assembledKids_count mv)]
  decide

theorem assembledParentCover (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ deepResiduals assembledKids, Cover (WeightedBound B) e.2) :
    Cover (WeightedBound B) p110 :=
  cover_of_deepCut assembledKids assembledKids_checked B hB hLeaves

theorem assembledExact (B : Nat) (hB : 7014 ≤ B)
    (hOther : ∀ e ∈ otherRoster, Cover (WeightedBound B) e.2)
    (hLeaves : ∀ e ∈ deepResiduals assembledKids, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_of_deepCut assembledKids assembledKids_checked B hB hOther hLeaves champ

theorem assembled_obligation_count :
    otherRoster.length + (deepResiduals assembledKids).length = {77+sum(counts)} := by
  rw [otherRoster_count, assembledResidual_count]

#print axioms assembledKids_checked
#print axioms assembledResidual_count
#print axioms assembledParentCover
#print axioms assembledExact
#print axioms assembled_obligation_count
end BB6.Agent7Raw110
"""
(ROOT / "Raw110DeepRoster.lean").write_text(body)
print("Retained descendants:", sum(counts), "from checked child count obligations")
