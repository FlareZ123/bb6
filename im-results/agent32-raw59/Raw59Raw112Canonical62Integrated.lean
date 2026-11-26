import Canonical64Raw120Integrated
import Raw59ParentCover
import Raw112ClosedCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent32Raw59Raw112Canonical62

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6.Agent3Canonical64Raw120
open BB6.Agent32Raw59
open BB6.Agent47Raw112

abbrev p59 : PartialMachine := BB6.Agent32Raw59.p59
abbrev p112 : PartialMachine := BB6.Agent47Raw112.parent

/-- Both parent cylinders have the standard first-one blank-start transition. -/
theorem p59_root :
    p59 initialSlot = some (some ⟨true,true,1⟩) := by
  decide

theorem p112_root :
    p112 initialSlot = some (some ⟨true,true,1⟩) := by
  decide

/-- Each independently source-certified parent occurs exactly once in Canonical64. -/
theorem p59_count :
    (BB6.Agent3Canonical64Raw120.roster64.filter
      (fun e => sameTable e.2 p59)).length = 1 := by
  decide

theorem p112_count :
    (BB6.Agent3Canonical64Raw120.roster64.filter
      (fun e => sameTable e.2 p112)).length = 1 := by
  decide

theorem p59_p112_distinct : p59 ≠ p112 := by
  decide

/-- Remove both accepted parent cylinders simultaneously from the exact 64-roster. -/
def parents : List PartialMachine := [p59, p112]

noncomputable def roster62 :=
  removeParents parents BB6.Agent3Canonical64Raw120.roster64

theorem count62 : roster62.length = 62 := by
  decide

/-- Lift Raw59's 4,200,000 Cover to the common 6,766,859 floor. -/
theorem p59_cover_at_common_floor :
    Cover (WeightedBound 6766859) p59 := by
  refine Cover.leaf p59 ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent32Raw59UpgradeAll.bound m hm k d hk hd)
    (by decide)

/-- Lift Raw112's 100,000 Cover to the same common floor. -/
theorem p112_cover_at_common_floor :
    Cover (WeightedBound 6766859) p112 := by
  refine Cover.leaf p112 ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent47Raw112.parent_cover.sound m hm k d hk hd)
    (by decide)

theorem parents_root :
    ∀ p ∈ parents, p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  simp only [parents, List.mem_cons, List.mem_singleton] at hp
  rcases hp with hp | hp
  · subst p
    exact p59_root
  · subst p
    exact p112_root

theorem parents_cover :
    ∀ p ∈ parents, Cover (WeightedBound 6766859) p := by
  intro p hp
  simp only [parents, List.mem_cons, List.mem_singleton] at hp
  rcases hp with hp | hp
  · subst p
    exact p59_cover_at_common_floor
  · subst p
    exact p112_cover_at_common_floor

/-- Two source-certified E1 sibling Covers consume two distinct entries of
    Canonical64, leaving 62 explicit quotient representatives. -/
theorem sound62_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster62, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound
    (parents := parents)
    (roster := BB6.Agent3Canonical64Raw120.roster64)
    BB6.Agent3Canonical64Raw120.sound64_integrated
  · exact parents_root
  · exact parents_cover

/-- Conditional exactness after both parent Covers are consumed: 62 residual
    Covers at the target bound and an attaining blank-start witness remain explicit. -/
theorem exact_at_target62 (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster62, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound62_integrated hLeaves champ

#print axioms p59_root
#print axioms p112_root
#print axioms p59_count
#print axioms p112_count
#print axioms p59_p112_distinct
#print axioms count62
#print axioms p59_cover_at_common_floor
#print axioms p112_cover_at_common_floor
#print axioms parents_root
#print axioms parents_cover
#print axioms sound62_integrated
#print axioms exact_at_target62

end BB6.Agent32Raw59Raw112Canonical62
