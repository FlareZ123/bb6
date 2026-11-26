import Canonical64Raw120Integrated
import Raw59ParentCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent32Raw59Canonical64

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6.Agent3Canonical64Raw120
open BB6.Agent32Raw59

/-- Raw59 has the same standard first-one blank-start transition. -/
theorem p59_root :
    p59 initialSlot = some (some ⟨true,true,1⟩) := by
  decide

/-- Raw59 is present exactly once in the source-accepted Canonical64 roster. -/
theorem p59_count :
    (BB6.Agent3Canonical64Raw120.roster64.filter
      (fun e => sameTable e.2 p59)).length = 1 := by
  decide

/-- Remove the independently source-certified Raw59 parent from Canonical64. -/
noncomputable def roster63 :=
  removeParents [p59] BB6.Agent3Canonical64Raw120.roster64

theorem count63 : roster63.length = 63 := by
  decide

/-- Lift the Raw59 4,200,000 parent Cover to the common 6,766,859 floor. -/
theorem parent_cover_at_common_floor :
    Cover (WeightedBound 6766859) p59 := by
  refine Cover.leaf p59 ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent32Raw59UpgradeAll.bound m hm k d hk hd)
    (by decide)

/-- Integrated Raw59 composition: the accepted Canonical64 theorem and the
    Raw59 parent Cover leave exactly 63 quotient representatives. -/
theorem sound63_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster63, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound
    (parents := [p59])
    (roster := BB6.Agent3Canonical64Raw120.roster64)
    BB6.Agent3Canonical64Raw120.sound64_integrated
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact p59_root
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact parent_cover_at_common_floor

/-- Conditional exactness after Raw59 is consumed: the 63 remaining Covers
    at the target bound and an attaining blank-start witness remain explicit. -/
theorem exact_at_target63 (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster63, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound63_integrated hLeaves champ

#print axioms p59_root
#print axioms p59_count
#print axioms count63
#print axioms parent_cover_at_common_floor
#print axioms sound63_integrated
#print axioms exact_at_target63

end BB6.Agent32Raw59Canonical64
