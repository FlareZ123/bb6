import Combined106Roster
import MixedBound109Composition

namespace BB6.Agent13MixedBound106

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent48DirectRoot
open BB6.CoverageAdapter

/-- Reuse the exact published champion score from the 109-residual adapter. -/
abbrev championScore : Nat := BB6.Agent13MixedBound109.championScore

/-- The champion is retained by the stronger 106-residual cut as well:
    every removed cylinder was already safe at 7014. -/
theorem champion_in_reduced_roster :
    ∃ e ∈ BB6.Agent47Combined106.reducedRoster, compatible e.2 championTable := by
  rcases BB6.Agent47Combined106.reduced_sound championTable
      BB6.Agent13MixedBound109.champion_compatible_root with hBound | hResidual
  · exact False.elim
      (BB6.Agent13MixedBound109.champion_not_weighted_7014 hBound)
  · exact hResidual

/-- The exact champion singleton is a concrete B-safe halting leaf, but does
    not discharge the larger retained cylinder containing it. -/
theorem champion_singleton_leaf :
    Cover (WeightedBound championScore)
      BB6.Agent13MixedBound109.championSingleton :=
  BB6.Agent13MixedBound109.champion_singleton_leaf

/-- The accepted 106-way dichotomy now has the correct maximality interface:
    the early 7014 branch lifts to B, while every retained residual is
    required directly at the exact champion score. -/
theorem cover_of_reduced_roster_at_champion_score
    (hLeaves : ∀ e ∈ BB6.Agent47Combined106.reducedRoster,
      Cover (WeightedBound championScore) e.2) :
    Cover (WeightedBound championScore) BB6.Agent50TNFPilot.root :=
  BB6.Agent13RosterComposition.cover_of_roster_dichotomy_mixed
    (Nat.le_of_lt BB6.Agent13MixedBound109.champion_score_gt_7014)
    BB6.Agent47Combined106.reduced_sound hLeaves

/-- Normalized certificate at the exact champion score, with 106 residual
    obligations rather than the earlier 109. -/
noncomputable def tnf_certificate_of_reduced_roster_at_champion_score
    (hLeaves : ∀ e ∈ BB6.Agent47Combined106.reducedRoster,
      Cover (WeightedBound championScore) e.2) :
    WeightedTNFCertificate championScore BB6.CoverageAdapter.firstOneCylinder 2 :=
  BB6.Agent13RosterComposition.tnf_certificate_of_roster_dichotomy_mixed
    (Nat.le_of_lt BB6.Agent13MixedBound109.champion_score_gt_7014)
    BB6.Agent47Combined106.reduced_sound hLeaves

/-- Conditional exact BB(6) from the 106 residual covers at B. -/
theorem exact_from_reduced_roster_at_champion_score
    (hLeaves : ∀ e ∈ BB6.Agent47Combined106.reducedRoster,
      Cover (WeightedBound championScore) e.2) :
    BB6.Coverage.ExactBB6 championScore :=
  BB6.Agent13RosterComposition.exact_from_roster_dichotomy_mixed
    (by decide)
    (Nat.le_of_lt BB6.Agent13MixedBound109.champion_score_gt_7014)
    BB6.Agent47Combined106.reduced_sound hLeaves champion_raw_witness

#print axioms BB6.Agent13MixedBound109.champion_score_gt_7014
#print axioms BB6.Agent13MixedBound109.champion_compatible_root
#print axioms BB6.Agent13MixedBound109.champion_not_weighted_7014
#print axioms BB6.Agent47Combined106.reduced_sound
#print axioms BB6.Agent13MixedBound109.champion_singleton_leaf
#print axioms BB6.Agent48DirectRoot.champion_raw_witness
#print axioms champion_in_reduced_roster
#print axioms champion_singleton_leaf
#print axioms cover_of_reduced_roster_at_champion_score
#print axioms tnf_certificate_of_reduced_roster_at_champion_score
#print axioms exact_from_reduced_roster_at_champion_score

end BB6.Agent13MixedBound106
