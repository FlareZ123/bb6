import Agent48RosterGraft
import WeightedFirstOneCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent48RosterGraftComposition

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent50TNFPilot
open BB6.Agent48RosterGraft

/-- If every residual cylinder in the adaptive graft has a weighted cover,
    the first-one root has a weighted cover. -/
theorem cover_of_graftedRoster
    (hLeaves : ∀ t ∈ graftedRoster,
      Cover (WeightedBound 7014) (unpackTable t)) :
    Cover (WeightedBound 7014) BB6.Agent50TNFPilot.root := by
  refine Cover.leaf _ ?_
  intro m hm
  rcases graftedRoster_sound_7014 m hm with hbound | ⟨t, ht, hcomp⟩
  · exact hbound
  · exact (hLeaves t ht).sound m hcomp

/-- Convert the root cover to the standard first-one cylinder at any larger
    weighted threshold. -/
theorem firstOne_cover_of_graftedRoster (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ t ∈ graftedRoster,
      Cover (WeightedBound 7014) (unpackTable t)) :
    Cover (WeightedBound B) firstOneCylinder := by
  refine Cover.leaf _ ?_
  intro m hm
  have hmRoot : compatible BB6.Agent50TNFPilot.root m := by
    simpa [BB6.Agent50TNFPilot.root] using hm
  exact weightedBound_mono hB ((cover_of_graftedRoster hLeaves).sound m hmRoot)

/-- The same normalization constructor used by Agent13, now parameterized by
    the 441-table adaptive residual frontier. -/
def grafted_tnf_certificate (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ t ∈ graftedRoster,
      Cover (WeightedBound 7014) (unpackTable t)) :
    WeightedTNFCertificate B firstOneCylinder 2 :=
  WeightedTNFCertificate.ofWeightedCover
    firstOneCylinder_tnf_root.1
    firstOneCylinder_tnf_root.2.1
    firstOneCylinder_tnf_root.2.2
    (firstOne_cover_of_graftedRoster B hB hLeaves)

/-- Conditional exact-BB(6) theorem: the only remaining inputs are weighted
    covers for the 441 residual cylinders and the already established champion. -/
theorem exact_from_graftedRoster (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ t ∈ graftedRoster,
      Cover (WeightedBound 7014) (unpackTable t))
    (champ : ∃ m : RawMachine, HaltsAt (tickRaw m) B) :
    ExactBB6 B :=
  exact_from_tnf_certificate B (by omega)
    (grafted_tnf_certificate B hB hLeaves) champ

#print axioms cover_of_graftedRoster
#print axioms grafted_tnf_certificate
#print axioms exact_from_graftedRoster

end BB6.Agent48RosterGraftComposition
