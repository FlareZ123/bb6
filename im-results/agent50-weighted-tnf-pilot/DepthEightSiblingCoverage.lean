import DepthEightSiblingData1
import DepthEightSiblingData2
import DepthEightSiblingData3
import DepthEightSiblingData4
import DepthEightFAR
import C1Growth

set_option maxRecDepth 24000
set_option maxHeartbeats 0

namespace BB6.Agent50RecursiveResidual
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent50RootFrontier
open BB6.Agent7FAR.DepthEight

def siblingData : List CheckedTree :=
  siblingData1 ++ siblingData2 ++ siblingData3 ++ siblingData4

/-- Four exact one-hole residuals already have independently Lean-checked
    infinite-tape FAR proofs. They are consumed only by exact packed-table
    equality; the candidate generator and its search metadata are not trusted. -/
def farLeaves : List PartialMachine := [p85_0, p114_0, p116_0, p128_0]

theorem farLeaves_never (p : PartialMachine) (m : Machine)
    (hp : p ∈ farLeaves) (hm : compatible p m) : NeverHalts m := by
  simp [farLeaves] at hp
  rcases hp with h | h | h | h
  · subst p
    exact p85_0_neverHalts m hm
  · subst p
    exact p114_0_neverHalts m hm
  · subst p
    exact p116_0_neverHalts m hm
  · subst p
    exact p128_0_neverHalts m hm

def farCovered (t : PackedTable) : Bool :=
  farLeaves.any (fun p => decide (packTable p = t))

theorem farCovered_never (t : PackedTable) (m : Machine)
    (h : farCovered t = true) (hm : compatible (unpackTable t) m) :
    NeverHalts m := by
  obtain ⟨p,hp,he⟩ := List.any_eq_true.mp h
  have ht : packTable p = t := of_decide_eq_true he
  exact farLeaves_never p m hp
    (by simpa only [← ht, unpack_packTable] using hm)

def replaceResidual (t : PackedTable) : List PackedTable :=
  match siblingData.find? (fun e => decide (e.table = t)) with
  | none => [t]
  | some e =>
      (e.tree.packedResiduals (unpackTable t)).filter (fun q => !farCovered q)

/-- Exact equality binds each untrusted generated tree to the live frontier.
    A missing matching certificate retains the original cylinder. -/
theorem replaceResidual_sound (t : PackedTable) (m : Machine)
    (hm : compatible (unpackTable t) m) :
    WeightedBound 400 m ∨ ∃ q ∈ replaceResidual t, compatible (unpackTable q) m := by
  cases he : siblingData.find? (fun e => decide (e.table = t)) with
  | none =>
    exact Or.inr ⟨t,by simp [replaceResidual,he],hm⟩
  | some e =>
    have hp : decide (e.table = t) = true :=
      List.find?_some (p := fun x : CheckedTree => decide (x.table = t)) he
    have htable : e.table = t := of_decide_eq_true hp
    have hcheck : e.tree.check 400 (unpackTable t) = true := by
      simpa only [htable] using e.checked
    rcases e.tree.packed_sound 400 (unpackTable t) hcheck m hm with hb | ⟨q,hq,hqc⟩
    · exact Or.inl hb
    · cases hf : farCovered q with
      | true =>
          exact Or.inl (weighted_never 400 m (farCovered_never q m hf hqc))
      | false =>
          have hq' : q ∈ replaceResidual t := by
            simpa [replaceResidual, he] using
              (List.mem_filter.mpr ⟨hq, by simp [hf]⟩ : q ∈
                (e.tree.packedResiduals (unpackTable t)).filter (fun q => !farCovered q))
          exact Or.inr ⟨q,hq',hqc⟩

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

def siblingOpenRawRoster : List PackedTable :=
  siblingData.flatMap fun e => e.tree.packedResiduals (unpackTable e.table)

/-- Every imported FAR table is an actual open leaf of the checked depth-eight
    sibling trees, not merely a table found in an external candidate roster. -/
theorem farLeaves_in_siblingOpenRawRoster :
    ∀ p ∈ farLeaves, packTable p ∈ siblingOpenRawRoster := by decide

def siblingOpenRoster : List PackedTable :=
  siblingOpenRawRoster.filter (fun t => !farCovered t)

theorem siblingOpenRoster_count : siblingOpenRoster.length = 103 := by decide
theorem siblingOpenRoster_one_hole : siblingOpenRoster.countP (fun t => holeCount t == 1) = 97 := by decide
theorem siblingOpenRoster_two_hole : siblingOpenRoster.countP (fun t => holeCount t == 2) = 6 := by decide
theorem siblingOpenRoster_mass : rawMass siblingOpenRoster = 6175 := by decide
theorem refinedRootRoster_count : refinedRootRoster.length = 227 := by decide

#print axioms farLeaves_never
#print axioms farCovered_never
#print axioms replaceResidual_sound
#print axioms refinedRootRoster_sound
#print axioms farLeaves_in_siblingOpenRawRoster
#print axioms siblingOpenRoster_count
#print axioms siblingOpenRoster_mass
#print axioms refinedRootRoster_count

inductive GrowthWitness where
  | ones (i : Fin 4)
  | triple (w : Bool)

def GrowthWitness.table : GrowthWitness → PartialMachine
  | .ones i => BB6Coverage.Agent50OnesSweep.table i
  | .triple w => BB6Coverage.Agent50TripleSweep.table w

theorem GrowthWitness.never (w : GrowthWitness) (m : Machine)
    (hm : compatible w.table m) : NeverHalts m := by
  cases w with
  | ones i => exact BB6Coverage.Agent50OnesSweep.never i m hm
  | triple b => exact BB6Coverage.Agent50TripleSweep.never b m hm

def growthWitnesses : List GrowthWitness :=
  (List.finRange 4).map GrowthWitness.ones ++ [.triple false,.triple true]

def growthCovered (t : PackedTable) : Bool :=
  growthWitnesses.any (fun w => decide (packTable w.table = t))

theorem growthCovered_never (t : PackedTable) (m : Machine)
    (h : growthCovered t = true) (hm : compatible (unpackTable t) m) :
    NeverHalts m := by
  obtain ⟨w,hw,he⟩ := List.any_eq_true.mp h
  have ht : packTable w.table = t := of_decide_eq_true he
  exact w.never m (by simpa only [← ht,unpack_packTable] using hm)

def finalRootRoster : List PackedTable :=
  refinedRootRoster.filter (fun t => !growthCovered t)

def siblingFinalRoster : List PackedTable :=
  siblingOpenRoster.filter (fun t => !growthCovered t)

theorem finalRootRoster_sound :
    ∀ m, compatible root m → WeightedBound 400 m ∨
      ∃ q ∈ finalRootRoster, compatible (unpackTable q) m := by
  intro m hm
  rcases refinedRootRoster_sound m hm with hb | ⟨q,hq,hc⟩
  · exact Or.inl hb
  · cases hg : growthCovered q with
    | true => exact Or.inl (weighted_never 400 m (growthCovered_never q m hg hc))
    | false => exact Or.inr ⟨q,List.mem_filter.mpr ⟨hq,by simp [hg]⟩,hc⟩

theorem siblingFinalRoster_count : siblingFinalRoster.length = 97 := by decide
theorem siblingFinalRoster_mass : rawMass siblingFinalRoster = 2425 := by decide
theorem finalRootRoster_count : finalRootRoster.length = 221 := by decide

#print axioms growthCovered_never
#print axioms finalRootRoster_sound
#print axioms siblingFinalRoster_mass

end BB6.Agent50RecursiveResidual
