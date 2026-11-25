import DepthEightSiblingCoverage
import DepthEightLarge
import DepthEightXL
import Final126

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31DepthEightSiblingClosure

open BB6Coverage
open BB6.Agent50RecursiveResidual
open BB6.Agent50RootFrontier
open BB6.Agent50TNFPilot

/-- The 42 large-DFA and nine XL-DFA source-accepted leaves, plus the
    independently source-accepted tree126 recurrence. These are added to the
    existing 84-leaf FAR roster; exact table membership is checked below. -/
def extraFarLeaves : List FARLeaf := [
  ⟨BB6.Agent7FAR.DepthEightLarge.p1, BB6.Agent7FAR.DepthEightLarge.p1_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p2, BB6.Agent7FAR.DepthEightLarge.p2_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p3, BB6.Agent7FAR.DepthEightLarge.p3_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p4, BB6.Agent7FAR.DepthEightLarge.p4_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p5, BB6.Agent7FAR.DepthEightLarge.p5_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p6, BB6.Agent7FAR.DepthEightLarge.p6_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p8, BB6.Agent7FAR.DepthEightLarge.p8_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p9, BB6.Agent7FAR.DepthEightLarge.p9_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p10, BB6.Agent7FAR.DepthEightLarge.p10_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p11, BB6.Agent7FAR.DepthEightLarge.p11_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p12, BB6.Agent7FAR.DepthEightLarge.p12_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p13, BB6.Agent7FAR.DepthEightLarge.p13_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p14, BB6.Agent7FAR.DepthEightLarge.p14_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p19, BB6.Agent7FAR.DepthEightLarge.p19_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p20, BB6.Agent7FAR.DepthEightLarge.p20_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p21, BB6.Agent7FAR.DepthEightLarge.p21_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p25, BB6.Agent7FAR.DepthEightLarge.p25_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p26, BB6.Agent7FAR.DepthEightLarge.p26_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p27, BB6.Agent7FAR.DepthEightLarge.p27_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p28, BB6.Agent7FAR.DepthEightLarge.p28_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p29, BB6.Agent7FAR.DepthEightLarge.p29_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p30, BB6.Agent7FAR.DepthEightLarge.p30_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p31, BB6.Agent7FAR.DepthEightLarge.p31_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p32, BB6.Agent7FAR.DepthEightLarge.p32_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p33, BB6.Agent7FAR.DepthEightLarge.p33_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p34, BB6.Agent7FAR.DepthEightLarge.p34_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p35, BB6.Agent7FAR.DepthEightLarge.p35_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p36, BB6.Agent7FAR.DepthEightLarge.p36_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p37, BB6.Agent7FAR.DepthEightLarge.p37_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p38, BB6.Agent7FAR.DepthEightLarge.p38_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p39, BB6.Agent7FAR.DepthEightLarge.p39_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p40, BB6.Agent7FAR.DepthEightLarge.p40_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p41, BB6.Agent7FAR.DepthEightLarge.p41_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p42, BB6.Agent7FAR.DepthEightLarge.p42_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p43, BB6.Agent7FAR.DepthEightLarge.p43_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p44, BB6.Agent7FAR.DepthEightLarge.p44_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p45, BB6.Agent7FAR.DepthEightLarge.p45_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p47, BB6.Agent7FAR.DepthEightLarge.p47_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p48, BB6.Agent7FAR.DepthEightLarge.p48_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p49, BB6.Agent7FAR.DepthEightLarge.p49_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p51, BB6.Agent7FAR.DepthEightLarge.p51_never⟩,
  ⟨BB6.Agent7FAR.DepthEightLarge.p52, BB6.Agent7FAR.DepthEightLarge.p52_never⟩,
  ⟨BB6.Agent7FAR.DepthEightXL.p1, BB6.Agent7FAR.DepthEightXL.p1_never⟩,
  ⟨BB6.Agent7FAR.DepthEightXL.p2, BB6.Agent7FAR.DepthEightXL.p2_never⟩,
  ⟨BB6.Agent7FAR.DepthEightXL.p3, BB6.Agent7FAR.DepthEightXL.p3_never⟩,
  ⟨BB6.Agent7FAR.DepthEightXL.p4, BB6.Agent7FAR.DepthEightXL.p4_never⟩,
  ⟨BB6.Agent7FAR.DepthEightXL.p5, BB6.Agent7FAR.DepthEightXL.p5_never⟩,
  ⟨BB6.Agent7FAR.DepthEightXL.p6, BB6.Agent7FAR.DepthEightXL.p6_never⟩,
  ⟨BB6.Agent7FAR.DepthEightXL.p7, BB6.Agent7FAR.DepthEightXL.p7_never⟩,
  ⟨BB6.Agent7FAR.DepthEightXL.p8, BB6.Agent7FAR.DepthEightXL.p8_never⟩,
  ⟨BB6.Agent7FAR.DepthEightXL.p9, BB6.Agent7FAR.DepthEightXL.p9_never⟩,
  ⟨BB6Coverage.Agent6Final126.M, BB6Coverage.Agent6Final126.never⟩
]

def extraFarCovered (t : PackedTable) : Bool :=
  extraFarLeaves.any (fun leaf => decide (packTable leaf.val = t))

def farCoveredPlus (t : PackedTable) : Bool :=
  farCovered t || extraFarCovered t

theorem extraFarCovered_never (t : PackedTable) (m : Machine)
    (h : extraFarCovered t = true) (hm : compatible (unpackTable t) m) :
    NeverHalts m := by
  obtain ⟨leaf, hleaf, he⟩ := List.any_eq_true.mp h
  have ht : packTable leaf.val = t := of_decide_eq_true he
  exact leaf.property m (by simpa only [← ht, unpack_packTable] using hm)

theorem farCoveredPlus_never (t : PackedTable) (m : Machine)
    (h : farCoveredPlus t = true) (hm : compatible (unpackTable t) m) :
    NeverHalts m := by
  cases hold : farCovered t with
  | true => exact farCovered_never t m hold hm
  | false =>
      have hnew : extraFarCovered t = true := by
        simpa [farCoveredPlus, hold] using h
      exact extraFarCovered_never t m hnew hm

/-- The new candidate tables all bind to actual leaves of the four checked
    depth-eight sibling trees. No candidate is counted by label alone. -/
theorem extraFarLeaves_in_siblingOpenRawRoster :
    ∀ leaf ∈ extraFarLeaves,
      packTable leaf.val ∈ siblingOpenRawRoster := by
  decide

def siblingOpenRosterPlus : List PackedTable :=
  siblingOpenRawRoster.filter (fun t => !farCoveredPlus t)

def siblingFinalRosterPlus : List PackedTable :=
  siblingOpenRosterPlus.filter (fun t => !growthCovered t)

/-- The 51 new FAR leaves plus tree126 leave only the six two-hole growth
    leaves in the sibling roster. -/
theorem siblingOpenRosterPlus_count : siblingOpenRosterPlus.length = 6 := by
  decide

theorem siblingOpenRosterPlus_one_hole :
    siblingOpenRosterPlus.countP (fun t => holeCount t == 1) = 0 := by
  decide

theorem siblingOpenRosterPlus_two_hole :
    siblingOpenRosterPlus.countP (fun t => holeCount t == 2) = 6 := by
  decide

/-- The six existing growth witnesses close the remaining two-hole leaves:
    the complete depth-eight sibling subfrontier is now empty. -/
theorem siblingFinalRosterPlus_count : siblingFinalRosterPlus.length = 0 := by
  decide

def replaceResidualPlus (t : PackedTable) : List PackedTable :=
  (replaceResidual t).filter (fun q => !extraFarCovered q)

theorem replaceResidualPlus_sound (t : PackedTable) (m : Machine)
    (hm : compatible (unpackTable t) m) :
    WeightedBound 400 m ∨
      ∃ q ∈ replaceResidualPlus t, compatible (unpackTable q) m := by
  rcases replaceResidual_sound t m hm with hb | ⟨q, hq, hqc⟩
  · exact Or.inl hb
  · cases hnew : extraFarCovered q with
    | true =>
        exact Or.inl (weighted_never 400 m (extraFarCovered_never q m hnew hqc))
    | false =>
        exact Or.inr ⟨q, by simp [replaceResidualPlus, hnew, hq], hqc⟩

def refinedRootRosterPlus : List PackedTable :=
  reducedRootRoster.flatMap fun e => replaceResidualPlus e.2

theorem refinedRootRosterPlus_sound :
    ∀ m, compatible root m →
      WeightedBound 400 m ∨
        ∃ q ∈ refinedRootRosterPlus, compatible (unpackTable q) m := by
  intro m hm
  rcases reducedRootRoster_sound m hm with hb | ⟨e, hmem, hcomp⟩
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · rcases replaceResidualPlus_sound e.2 m hcomp with hb | ⟨q, hq, hqc⟩
    · exact Or.inl hb
    · exact Or.inr ⟨q, List.mem_flatMap.mpr ⟨e, hmem, hq⟩, hqc⟩

def finalRootRosterPlus : List PackedTable :=
  refinedRootRosterPlus.filter (fun t => !growthCovered t)

theorem finalRootRosterPlus_sound :
    ∀ m, compatible root m →
      WeightedBound 400 m ∨
        ∃ q ∈ finalRootRosterPlus, compatible (unpackTable q) m := by
  intro m hm
  rcases refinedRootRosterPlus_sound m hm with hb | ⟨q, hq, hc⟩
  · exact Or.inl hb
  · cases hg : growthCovered q with
    | true =>
        exact Or.inl (weighted_never 400 m (growthCovered_never q m hg hc))
    | false =>
        exact Or.inr ⟨q, List.mem_filter.mpr ⟨hq, by simp [hg]⟩, hc⟩

/-- Closing the 17-leaf sibling remainder reduces the checked root roster
    from 141 to 124 residual tables. -/
theorem finalRootRosterPlus_count : finalRootRosterPlus.length = 124 := by
  decide

#print axioms extraFarLeaves_in_siblingOpenRawRoster
#print axioms siblingOpenRosterPlus_count
#print axioms siblingFinalRosterPlus_count
#print axioms refinedRootRosterPlus_sound
#print axioms finalRootRosterPlus_sound
#print axioms finalRootRosterPlus_count

end BB6.Agent31DepthEightSiblingClosure
