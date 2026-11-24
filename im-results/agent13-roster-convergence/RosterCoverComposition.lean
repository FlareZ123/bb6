import FourHoleResidualRoster
import WeightedFirstOneCover

namespace BB6.Agent13RosterComposition

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent31FourHoleRoster

/-- The accepted 124-cylinder dichotomy becomes a root Cover as soon as every
    retained residual cylinder has its own checked weighted-safety Cover. -/
theorem cover_of_remaining_roster
    (hLeaves : ∀ e ∈ remainingRootRoster,
      Cover (WeightedBound 395) e.2) :
    Cover (WeightedBound 395) BB6.Agent50TNFPilot.root := by
  refine Cover.leaf _ ?_
  intro m hm
  rcases remainingRootRoster_sound m hm with hBound | ⟨e, he, hcompat⟩
  · exact hBound
  · exact (hLeaves e he).sound m hcompat

/-- Lift the composed 395 root cover to any requested larger weighted bound. -/
theorem firstOne_cover_at_bound (B : Nat) (hB : 395 ≤ B)
    (hLeaves : ∀ e ∈ remainingRootRoster,
      Cover (WeightedBound 395) e.2) :
    Cover (WeightedBound B) BB6.CoverageAdapter.firstOneCylinder := by
  refine Cover.leaf _ ?_
  intro m hm
  have hmRoot : compatible BB6.Agent50TNFPilot.root m := by
    simpa [BB6.Agent50TNFPilot.root] using hm
  exact weightedBound_mono hB
    ((cover_of_remaining_roster hLeaves).sound m hmRoot)

/-- Turn the 124 residual Covers into the normalized certificate consumed by
    the existing universal raw-machine upper-bound theorem. -/
theorem tnf_certificate_of_remaining_roster (B : Nat) (hB : 395 ≤ B)
    (hLeaves : ∀ e ∈ remainingRootRoster,
      Cover (WeightedBound 395) e.2) :
    WeightedTNFCertificate B BB6.CoverageAdapter.firstOneCylinder 2 :=
  WeightedTNFCertificate.ofWeightedCover
    firstOneCylinder_tnf_root.1
    firstOneCylinder_tnf_root.2.1
    firstOneCylinder_tnf_root.2.2
    (firstOne_cover_at_bound B hB hLeaves)

/-- Conditional exact BB(6) theorem: the only remaining mathematical inputs
    are the 124 complete residual-cylinder safety Covers and the attained
    raw champion witness at B. No separate root tree or second enumeration is
    needed once those leaves are supplied. -/
theorem exact_from_remaining_roster (B : Nat) (hB : 395 ≤ B)
    (hLeaves : ∀ e ∈ remainingRootRoster,
      Cover (WeightedBound 395) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_tnf_certificate B (by omega)
    (tnf_certificate_of_remaining_roster B hB hLeaves) champ

#print axioms cover_of_remaining_roster
#print axioms firstOne_cover_at_bound
#print axioms tnf_certificate_of_remaining_roster
#print axioms exact_from_remaining_roster

end BB6.Agent13RosterComposition
