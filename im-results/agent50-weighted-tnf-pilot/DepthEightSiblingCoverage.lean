import DepthEightSiblingData1
import DepthEightSiblingData2
import DepthEightSiblingData3
import DepthEightSiblingData4
import DepthEightFAR
import DepthEightSMTBatch
import C1Growth

set_option maxRecDepth 24000
set_option maxHeartbeats 0

namespace BB6.Agent50RecursiveResidual
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent50RootFrontier
open BB6.Agent7FAR.DepthEight
open BB6.Agent7FAR.DepthEightSMTBatch

def siblingData : List CheckedTree :=
  siblingData1 ++ siblingData2 ++ siblingData3 ++ siblingData4

/-- A proof-carrying exact roster of one-hole FAR leaves. Membership
    retains each nonhalting theorem, so adding certificates does not require
    extending a large disjunction proof. -/
abbrev FARLeaf := {p : PartialMachine // ∀ m, compatible p m → NeverHalts m}

def farLeaves : List FARLeaf := [
  ⟨p85_0, p85_0_neverHalts⟩,
  ⟨p85_1, p85_1_neverHalts⟩,
  ⟨p85_2, p85_2_neverHalts⟩,
  ⟨p114_0, p114_0_neverHalts⟩,
  ⟨p116_0, p116_0_neverHalts⟩,
  ⟨p128_0, p128_0_neverHalts⟩,
  ⟨pRoster1, pRoster1_neverHalts⟩,
  ⟨pRoster2, pRoster2_neverHalts⟩,
  ⟨pRoster3, pRoster3_neverHalts⟩,
  ⟨pRoster6, pRoster6_neverHalts⟩,
  ⟨pRoster7, pRoster7_neverHalts⟩,
  ⟨pRoster8, pRoster8_neverHalts⟩,
  ⟨pRoster9, pRoster9_neverHalts⟩,
  ⟨pRoster10, pRoster10_neverHalts⟩,
  ⟨pRoster11, pRoster11_neverHalts⟩,
  ⟨pRoster12, pRoster12_neverHalts⟩,
  ⟨pRoster13, pRoster13_neverHalts⟩,
  ⟨pRoster15, pRoster15_neverHalts⟩,
  ⟨pRoster16, pRoster16_neverHalts⟩,
  ⟨pRoster17, pRoster17_neverHalts⟩,
  ⟨pRoster18, pRoster18_neverHalts⟩,
  ⟨pRoster19, pRoster19_neverHalts⟩,
  ⟨pRoster20, pRoster20_neverHalts⟩,
  ⟨pRoster21, pRoster21_neverHalts⟩,
  ⟨pRoster22, pRoster22_neverHalts⟩,
  ⟨pRoster23, pRoster23_neverHalts⟩,
  ⟨pRoster24, pRoster24_neverHalts⟩,
  ⟨pRoster25, pRoster25_neverHalts⟩,
  ⟨pRoster26, pRoster26_neverHalts⟩,
  ⟨pRoster27, pRoster27_neverHalts⟩,
  ⟨pRoster28, pRoster28_neverHalts⟩,
  ⟨pRoster29, pRoster29_neverHalts⟩,
  ⟨pRoster30, pRoster30_neverHalts⟩,
  ⟨pRoster31, pRoster31_neverHalts⟩,
  ⟨pRoster32, pRoster32_neverHalts⟩,
  ⟨pRoster33, pRoster33_neverHalts⟩,
  ⟨pRoster38, pRoster38_neverHalts⟩,
  ⟨pRoster40, pRoster40_neverHalts⟩,
  ⟨pRoster43, pRoster43_neverHalts⟩,
  ⟨pRoster45, pRoster45_neverHalts⟩,
  ⟨pRoster46, pRoster46_neverHalts⟩,
  ⟨pRoster47, pRoster47_neverHalts⟩,
  ⟨pRoster48, pRoster48_neverHalts⟩,
  ⟨pRoster49, pRoster49_neverHalts⟩,
  ⟨pRoster50, pRoster50_neverHalts⟩,
  ⟨pRoster51, pRoster51_neverHalts⟩,
  ⟨pRoster52, pRoster52_neverHalts⟩,
  ⟨pRoster53, pRoster53_neverHalts⟩,
  ⟨pRoster54, pRoster54_neverHalts⟩,
  ⟨pRoster55, pRoster55_neverHalts⟩,
  ⟨pRoster56, pRoster56_neverHalts⟩,
  ⟨pRoster57, pRoster57_neverHalts⟩,
  ⟨pRoster59, pRoster59_neverHalts⟩,
  ⟨pRoster60, pRoster60_neverHalts⟩,
  ⟨pRoster61, pRoster61_neverHalts⟩,
  ⟨pRoster62, pRoster62_neverHalts⟩,
  ⟨pRoster63, pRoster63_neverHalts⟩,
  ⟨pRoster64, pRoster64_neverHalts⟩,
  ⟨pRoster65, pRoster65_neverHalts⟩,
  ⟨pRoster66, pRoster66_neverHalts⟩,
  ⟨pRoster67, pRoster67_neverHalts⟩,
  ⟨pRoster68, pRoster68_neverHalts⟩,
  ⟨pRoster69, pRoster69_neverHalts⟩,
  ⟨pRoster70, pRoster70_neverHalts⟩,
  ⟨pRoster72, pRoster72_neverHalts⟩,
  ⟨pRoster73, pRoster73_neverHalts⟩,
  ⟨pRoster74, pRoster74_neverHalts⟩,
  ⟨pRoster75, pRoster75_neverHalts⟩,
  ⟨pRoster76, pRoster76_neverHalts⟩,
  ⟨pRoster77, pRoster77_neverHalts⟩,
  ⟨pRoster79, pRoster79_neverHalts⟩,
  ⟨pRoster81, pRoster81_neverHalts⟩,
  ⟨pRoster82, pRoster82_neverHalts⟩,
  ⟨pRoster83, pRoster83_neverHalts⟩,
  ⟨pRoster84, pRoster84_neverHalts⟩,
  ⟨pRoster85, pRoster85_neverHalts⟩,
  ⟨pRoster86, pRoster86_neverHalts⟩,
  ⟨pRoster87, pRoster87_neverHalts⟩,
  ⟨pRoster89, pRoster89_neverHalts⟩,
  ⟨pRoster90, pRoster90_neverHalts⟩,
  ⟨pRoster91, pRoster91_neverHalts⟩,
  ⟨pRoster92, pRoster92_neverHalts⟩,
  ⟨pRoster94, pRoster94_neverHalts⟩,
  ⟨pRoster95, pRoster95_neverHalts⟩
]

theorem farLeaves_never (leaf : FARLeaf) (m : Machine)
    (hm : compatible leaf.val m) : NeverHalts m :=
  leaf.property m hm

def farCovered (t : PackedTable) : Bool :=
  farLeaves.any (fun leaf => decide (packTable leaf.val = t))

theorem farCovered_never (t : PackedTable) (m : Machine)
    (h : farCovered t = true) (hm : compatible (unpackTable t) m) :
    NeverHalts m := by
  obtain ⟨leaf,hleaf,he⟩ := List.any_eq_true.mp h
  have ht : packTable leaf.val = t := of_decide_eq_true he
  exact farLeaves_never leaf m
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
    ∀ leaf ∈ farLeaves, packTable leaf.val ∈ siblingOpenRawRoster := by decide

def siblingOpenRoster : List PackedTable :=
  siblingOpenRawRoster.filter (fun t => !farCovered t)

theorem siblingOpenRoster_count : siblingOpenRoster.length = 23 := by decide
theorem siblingOpenRoster_one_hole : siblingOpenRoster.countP (fun t => holeCount t == 1) = 17 := by decide
theorem siblingOpenRoster_two_hole : siblingOpenRoster.countP (fun t => holeCount t == 2) = 6 := by decide
theorem siblingOpenRoster_mass : rawMass siblingOpenRoster = 4175 := by decide
theorem refinedRootRoster_count : refinedRootRoster.length = 147 := by decide

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

theorem siblingFinalRoster_count : siblingFinalRoster.length = 17 := by decide
theorem siblingFinalRoster_mass : rawMass siblingFinalRoster = 425 := by decide
theorem finalRootRoster_count : finalRootRoster.length = 141 := by decide

#print axioms growthCovered_never
#print axioms finalRootRoster_sound
#print axioms siblingFinalRoster_mass

end BB6.Agent50RecursiveResidual
