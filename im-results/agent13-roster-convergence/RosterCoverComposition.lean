import FourHoleResidualRoster
import WeightedFirstOneCover

namespace BB6.Agent13RosterComposition

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent31FourHoleRoster

/-- Generic root composition: a checked dichotomy into a finite residual
    roster, together with one weighted-safety Cover for each residual,
    produces a single Cover of the original root. -/
theorem cover_of_roster_dichotomy {C : Nat}
    {roster : List (List Move × PartialMachine)}
    (hRoot : ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound C m ∨ ∃ e ∈ roster, compatible e.2 m)
    (hLeaves : ∀ e ∈ roster, Cover (WeightedBound C) e.2) :
    Cover (WeightedBound C) BB6.Agent50TNFPilot.root := by
  refine Cover.leaf _ ?_
  intro m hm
  rcases hRoot m hm with hBound | ⟨e, he, hcompat⟩
  · exact hBound
  · exact (hLeaves e he).sound m hcompat

/-- WeightedBound is monotone in its numeric threshold. -/
theorem weightedBound_mono_local {A B : Nat} (hAB : A ≤ B)
    {m : Machine} (h : WeightedBound A m) : WeightedBound B m := by
  intro k d hk hd
  exact Nat.le_trans (h k d hk hd) hAB

/-- Lift a generic residual-roster dichotomy to a requested larger bound
    while retaining the exact first-one root used by normalization. -/
theorem firstOne_cover_of_roster_dichotomy {C B : Nat} (hCB : C ≤ B)
    {roster : List (List Move × PartialMachine)}
    (hRoot : ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound C m ∨ ∃ e ∈ roster, compatible e.2 m)
    (hLeaves : ∀ e ∈ roster, Cover (WeightedBound C) e.2) :
    Cover (WeightedBound B) BB6.CoverageAdapter.firstOneCylinder := by
  refine Cover.leaf _ ?_
  intro m hm
  have hmRoot : compatible BB6.Agent50TNFPilot.root m := by
    simpa [BB6.Agent50TNFPilot.root] using hm
  exact weightedBound_mono_local hCB
    ((cover_of_roster_dichotomy hRoot hLeaves).sound m hmRoot)

/-- Convert any sound root-dichotomy plus residual Covers into the normalized
    certificate consumed by the universal raw-machine upper-bound theorem. -/
noncomputable def tnf_certificate_of_roster_dichotomy {C B : Nat}
    (hCB : C ≤ B)
    {roster : List (List Move × PartialMachine)}
    (hRoot : ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound C m ∨ ∃ e ∈ roster, compatible e.2 m)
    (hLeaves : ∀ e ∈ roster, Cover (WeightedBound C) e.2) :
    WeightedTNFCertificate B BB6.CoverageAdapter.firstOneCylinder 2 :=
  WeightedTNFCertificate.ofWeightedCover
    firstOneCylinder_tnf_root.1
    firstOneCylinder_tnf_root.2.1
    firstOneCylinder_tnf_root.2.2
    (firstOne_cover_of_roster_dichotomy hCB hRoot hLeaves)

/-- Generic conditional exact-BB(6) theorem. The only inputs are a root
    dichotomy, safety Covers for its retained residuals, and the attained
    raw champion witness. -/
theorem exact_from_roster_dichotomy {C B : Nat} (hCB : C ≤ B)
    {roster : List (List Move × PartialMachine)}
    (hRoot : ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound C m ∨ ∃ e ∈ roster, compatible e.2 m)
    (hLeaves : ∀ e ∈ roster, Cover (WeightedBound C) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_tnf_certificate B (by omega)
    (tnf_certificate_of_roster_dichotomy hCB hRoot hLeaves) champ

/-- Specialization to Agent31's accepted 124-cylinder, 395-bound dichotomy. -/
theorem cover_of_remaining_roster
    (hLeaves : ∀ e ∈ remainingRootRoster,
      Cover (WeightedBound 395) e.2) :
    Cover (WeightedBound 395) BB6.Agent50TNFPilot.root :=
  cover_of_roster_dichotomy remainingRootRoster_sound hLeaves

theorem firstOne_cover_at_bound (B : Nat) (hB : 395 ≤ B)
    (hLeaves : ∀ e ∈ remainingRootRoster,
      Cover (WeightedBound 395) e.2) :
    Cover (WeightedBound B) BB6.CoverageAdapter.firstOneCylinder :=
  firstOne_cover_of_roster_dichotomy hB remainingRootRoster_sound hLeaves

noncomputable def tnf_certificate_of_remaining_roster (B : Nat) (hB : 395 ≤ B)
    (hLeaves : ∀ e ∈ remainingRootRoster,
      Cover (WeightedBound 395) e.2) :
    WeightedTNFCertificate B BB6.CoverageAdapter.firstOneCylinder 2 :=
  tnf_certificate_of_roster_dichotomy hB remainingRootRoster_sound hLeaves

theorem exact_from_remaining_roster (B : Nat) (hB : 395 ≤ B)
    (hLeaves : ∀ e ∈ remainingRootRoster,
      Cover (WeightedBound 395) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_roster_dichotomy hB remainingRootRoster_sound hLeaves champ

/-- The same 124 residual roster also has an accepted 7014-bound root
    dichotomy, which can consume the existing 7014 sibling certificates. -/
theorem cover_of_remaining_roster_7014
    (hLeaves : ∀ e ∈ remainingRootRoster,
      Cover (WeightedBound 7014) e.2) :
    Cover (WeightedBound 7014) BB6.Agent50TNFPilot.root :=
  cover_of_roster_dichotomy remainingRootRoster_sound_7014 hLeaves

theorem firstOne_cover_at_bound_7014 (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ remainingRootRoster,
      Cover (WeightedBound 7014) e.2) :
    Cover (WeightedBound B) BB6.CoverageAdapter.firstOneCylinder :=
  firstOne_cover_of_roster_dichotomy hB remainingRootRoster_sound_7014 hLeaves

noncomputable def tnf_certificate_of_remaining_roster_7014
    (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ remainingRootRoster,
      Cover (WeightedBound 7014) e.2) :
    WeightedTNFCertificate B BB6.CoverageAdapter.firstOneCylinder 2 :=
  tnf_certificate_of_roster_dichotomy hB remainingRootRoster_sound_7014 hLeaves

theorem exact_from_remaining_roster_7014 (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ remainingRootRoster,
      Cover (WeightedBound 7014) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_roster_dichotomy hB remainingRootRoster_sound_7014 hLeaves champ

#print axioms cover_of_roster_dichotomy
#print axioms exact_from_roster_dichotomy
#print axioms exact_from_remaining_roster
#print axioms exact_from_remaining_roster_7014

end BB6.Agent13RosterComposition
