import DepthEightSiblingData1
import DepthEightSiblingData2
import DepthEightSiblingData3
import DepthEightSiblingData4

set_option maxRecDepth 24000
set_option maxHeartbeats 0

namespace BB6.Agent50RecursiveResidual
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent50RootFrontier

def siblingData : List CheckedTree :=
  siblingData1 ++ siblingData2 ++ siblingData3 ++ siblingData4

def replaceResidual (t : PackedTable) : List PackedTable :=
  match siblingData.find? (fun e => decide (e.table = t)) with
  | none => [t]
  | some e => e.tree.packedResiduals (unpackTable t)

/-- Exact equality binds each untrusted generated tree to the live frontier.
    A missing matching certificate retains the original cylinder. -/
theorem replaceResidual_sound (t : PackedTable) (m : Machine)
    (hm : compatible (unpackTable t) m) :
    WeightedBound 400 m ∨ ∃ q ∈ replaceResidual t, compatible (unpackTable q) m := by
  cases he : siblingData.find? (fun e => decide (e.table = t)) with
  | none =>
    exact Or.inr ⟨t,by simp [replaceResidual,he],hm⟩
  | some e =>
    have htable : e.table = t := of_decide_eq_true (List.find?_some he)
    have hcheck : e.tree.check 400 (unpackTable t) = true := by
      simpa only [htable] using e.checked
    simpa only [replaceResidual,he] using e.tree.packed_sound 400 (unpackTable t) hcheck m hm

def refinedRootRoster : List PackedTable :=
  reducedRootRoster.flatMap fun e => replaceResidual e.2

theorem refinedRootRoster_sound :
    ∀ m, compatible root m → WeightedBound 400 m ∨
      ∃ q ∈ refinedRootRoster, compatible (unpackTable q) m := by
  intro m hm
  rcases reducedRootRoster_sound m hm with hb | ⟨e,hmem,hcomp⟩
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · rcases replaceResidual_sound e.2 m hcomp with hb | ⟨q,hq,hqc⟩
    · exact Or.inl hb
    · exact Or.inr ⟨q,List.mem_flatMap.mpr ⟨e,hmem,hq⟩,hqc⟩

def holeCount (t : PackedTable) : Nat := t.countP (·.isNone)

/-- Number of concrete raw tables extending a twelve-slot partial table.
    This is a diagnostic mass count, not a global coverage premise. -/
def rawMass (xs : List PackedTable) : Nat :=
  (xs.map (fun t => 25 ^ holeCount t)).sum

def siblingOpenRoster : List PackedTable :=
  siblingData.flatMap fun e => e.tree.packedResiduals (unpackTable e.table)

theorem siblingOpenRoster_count : siblingOpenRoster.length = 107 := by decide
theorem siblingOpenRoster_one_hole : siblingOpenRoster.countP (fun t => holeCount t == 1) = 101 := by decide
theorem siblingOpenRoster_two_hole : siblingOpenRoster.countP (fun t => holeCount t == 2) = 6 := by decide
theorem siblingOpenRoster_mass : rawMass siblingOpenRoster = 6275 := by decide
theorem refinedRootRoster_count : refinedRootRoster.length = 231 := by decide

#print axioms replaceResidual_sound
#print axioms refinedRootRoster_sound
#print axioms siblingOpenRoster_count
#print axioms siblingOpenRoster_mass
#print axioms refinedRootRoster_count
end BB6.Agent50RecursiveResidual
