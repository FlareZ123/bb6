import FiveHoleRoster
import RosterCoverComposition

namespace BB6.Agent13FiveHoleComposition

open BB6Coverage
open BB6.Agent13BlankDelay

/-- The three exact five-hole certificates reduce the accepted first-one
    frontier from 124 residual cylinders to 121.  This is still conditional:
    each of the 121 retained cylinders needs its own weighted-safety Cover. -/
theorem cover_of_five_hole_reduced_roster
    (hLeaves : ∀ e ∈ BB6.Agent10FiveHoleRoster.reducedRoster,
      Cover (WeightedBound 395) e.2) :
    Cover (WeightedBound 395) BB6.Agent50TNFPilot.root :=
  BB6.Agent13RosterComposition.cover_of_roster_dichotomy
    BB6.Agent10FiveHoleRoster.reduced_sound hLeaves

/-- Lift the 121-cylinder cut to any larger weighted bound. -/
theorem firstOne_cover_of_five_hole_reduced_roster (B : Nat) (hB : 395 ≤ B)
    (hLeaves : ∀ e ∈ BB6.Agent10FiveHoleRoster.reducedRoster,
      Cover (WeightedBound 395) e.2) :
    Cover (WeightedBound B) BB6.CoverageAdapter.firstOneCylinder :=
  BB6.Agent13RosterComposition.firstOne_cover_of_roster_dichotomy
    hB BB6.Agent10FiveHoleRoster.reduced_sound hLeaves

/-- Normalized certificate interface for the reduced 121-cylinder frontier. -/
noncomputable def tnf_certificate_of_five_hole_reduced_roster
    (B : Nat) (hB : 395 ≤ B)
    (hLeaves : ∀ e ∈ BB6.Agent10FiveHoleRoster.reducedRoster,
      Cover (WeightedBound 395) e.2) :
    WeightedTNFCertificate B BB6.CoverageAdapter.firstOneCylinder 2 :=
  BB6.Agent13RosterComposition.tnf_certificate_of_roster_dichotomy
    hB BB6.Agent10FiveHoleRoster.reduced_sound hLeaves

/-- Conditional exact-BB(6) theorem with only the 121 retained safety
    obligations and the already checked champion attainment as premises. -/
theorem exact_from_five_hole_reduced_roster (B : Nat) (hB : 395 ≤ B)
    (hLeaves : ∀ e ∈ BB6.Agent10FiveHoleRoster.reducedRoster,
      Cover (WeightedBound 395) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  BB6.Agent13RosterComposition.exact_from_roster_dichotomy
    (by decide) hB BB6.Agent10FiveHoleRoster.reduced_sound hLeaves champ

#print axioms BB6.Agent10FiveHoleRoster.reduced_count
#print axioms BB6.Agent10FiveHoleRoster.reduced_sound
#print axioms cover_of_five_hole_reduced_roster
#print axioms exact_from_five_hole_reduced_roster

end BB6.Agent13FiveHoleComposition
