import Canonical78Roster
import TM63RawUpperInterface

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical78Exact

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6ChampionArithmetic
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent48DirectRoot
open BB6.Agent47CanonicalFrontier

/-- The attained champion score in the original raw semantics. -/
abbrev championScore : Nat := proposedTM63Moves + 7

theorem champion_score_gt_7014 : 7014 < championScore := by
  have hroot : 27959 ≤ threeSectionMoves 27959 3 7 6 63 + 7 :=
    BB6.Agent48TM63RawUpperInterface.rootSteps_le_score 27959 3 7 6 63
  change 7014 < proposedTM63Moves + 7
  rw [← threeSectionMoves_root]
  omega

/-- The literal champion extends the authentic first-one root. -/
theorem champion_compatible_root :
    compatible BB6.Agent50TNFPilot.root championTable := by
  change compatible BB6.CoverageAdapter.firstOneCylinder championTable
  exact (compatible_refine_iff emptyTable championTable initialSlot rfl
    (some ⟨true,true,(1 : Fin 6)⟩)).mpr
      ⟨empty_compatible championTable, by decide [championTable]⟩

/-- The champion's exact halt at B rules out the early 7014 bound. -/
theorem champion_not_weighted_7014 :
    ¬ WeightedBound 7014 championTable := by
  intro h
  have hzero : 0 ∈ delays (zeroNext championTable) 0 := by
    rw [champion_delays_exact]
    simp
  have hsmall := h (proposedTM63Moves + 6) 0 hzero
  omega

/-- Consequently the canonical 78-way dichotomy places the champion in a
    retained quotient-compatible residual, not in the early bounded branch. -/
theorem champion_in_canonical_roster :
    ∃ e ∈ BB6.Agent47Canonical78.roster,
      TNFQuotientCompatible e.2 championTable := by
  rcases BB6.Agent47Canonical78.roster_sound championTable champion_compatible_root
      with hBound | hResidual
  · exact False.elim (champion_not_weighted_7014 hBound)
  · exact hResidual

/-- The 78 quotient-residual covers at B yield a root cover at B. -/
theorem cover_at_champion_score
    (hLeaves : ∀ e ∈ BB6.Agent47Canonical78.roster,
      Cover (WeightedBound championScore) e.2) :
    Cover (WeightedBound championScore) BB6.CoverageAdapter.firstOneCylinder :=
  BB6.Agent47Canonical78.cover_at_target championScore
    (Nat.le_of_lt champion_score_gt_7014) hLeaves

/-- Ingest the already source-accepted raw champion witness: 78 B-bound
    quotient-residual Covers suffice for exact BB(6) at the attained score. -/
theorem exact_from_canonical78_at_champion_score
    (hLeaves : ∀ e ∈ BB6.Agent47Canonical78.roster,
      Cover (WeightedBound championScore) e.2) :
    BB6.Coverage.ExactBB6 championScore :=
  BB6.Agent47Canonical78.exact_at_target championScore
    (Nat.le_of_lt champion_score_gt_7014) hLeaves champion_raw_witness

#print axioms champion_score_gt_7014
#print axioms champion_compatible_root
#print axioms champion_not_weighted_7014
#print axioms champion_in_canonical_roster
#print axioms champion_raw_witness
#print axioms cover_at_champion_score
#print axioms exact_from_canonical78_at_champion_score

end BB6.Agent31Canonical78Exact
