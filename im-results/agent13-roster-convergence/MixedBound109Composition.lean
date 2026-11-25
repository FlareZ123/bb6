import Combined109Roster
import TM63RawUpperInterface

namespace BB6.Agent13MixedBound109

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent48DirectRoot
open BB6ChampionArithmetic
open BB6.Agent47Combined109

/-- The exact published champion score. -/
abbrev championScore : Nat := proposedTM63Moves + 7

/-- The champion has no incoming zero-writing delay at its A/0 root. -/
theorem champion_score_gt_7014 : 7014 < championScore := by
  have hroot : 27959 ≤ threeSectionMoves 27959 3 7 6 63 + 7 := by
    simp only [threeSectionMoves]
    omega
  change 7014 < proposedTM63Moves + 7
  rw [← threeSectionMoves_root]
  omega

/-- The champion is compatible with the authentic first-one root. -/
theorem champion_compatible_root :
    compatible BB6.Agent50TNFPilot.root championTable := by
  change compatible BB6.CoverageAdapter.firstOneCylinder championTable
  exact (compatible_refine_iff emptyTable championTable initialSlot rfl
    (some ⟨true,true,(1 : Fin 6)⟩)).mpr
      ⟨empty_compatible championTable, by decide [championTable]⟩

/-- The exact source halting run and its exact delay list show that the
    champion cannot belong to the early 7014-bounded branch. -/
theorem champion_not_weighted_7014 :
    ¬ WeightedBound 7014 championTable := by
  intro h
  have hd : 0 ∈ delays (zeroNext championTable) 0 := by
    rw [champion_delays_exact]
    simp
  have hscore := h (proposedTM63Moves + 6) 0 champion_halts_exact hd
  have hB : 7014 < proposedTM63Moves + 7 := by
    simpa [championScore] using champion_score_gt_7014
  omega

/-- Therefore the accepted 109-way dichotomy places the actual champion in
    one of its retained residual cylinders. -/
theorem champion_in_reduced_roster :
    ∃ e ∈ reducedRoster, compatible e.2 championTable := by
  rcases reduced_sound championTable champion_compatible_root with hBound | hResidual
  · exact False.elim (champion_not_weighted_7014 hBound)
  · exact hResidual

/-- A concrete larger-bound halter leaf: the singleton complete table of the
    champion is safe at its exact score, but is not safe at 7014. -/
def championSingleton : PartialMachine :=
  fun s => some (championTable s)

theorem champion_singleton_leaf :
    Cover (WeightedBound championScore) championSingleton := by
  refine Cover.leaf _ ?_
  intro m hm
  have hEq : m = championTable := by
    funext s
    exact hm s (championTable s) rfl
  subst m
  exact champion_weighted_bound

/-- If every retained 109-cylinder is certified at the attained score B,
    the mixed-bound adapter produces the required first-one root Cover.
    Only the already-discharged 7014 branch is lifted; residual leaves are
    consumed directly at B. -/
theorem cover_of_reduced_roster_at_champion_score
    (hLeaves : ∀ e ∈ reducedRoster,
      Cover (WeightedBound championScore) e.2) :
    Cover (WeightedBound championScore) BB6.Agent50TNFPilot.root :=
  BB6.Agent13RosterComposition.cover_of_roster_dichotomy_mixed
    (Nat.le_of_lt champion_score_gt_7014) reduced_sound hLeaves

/-- The corresponding normalized certificate at the exact champion score. -/
noncomputable def tnf_certificate_of_reduced_roster_at_champion_score
    (hLeaves : ∀ e ∈ reducedRoster,
      Cover (WeightedBound championScore) e.2) :
    WeightedTNFCertificate championScore
      BB6.CoverageAdapter.firstOneCylinder 2 :=
  BB6.Agent13RosterComposition.tnf_certificate_of_roster_dichotomy_mixed
    (Nat.le_of_lt champion_score_gt_7014) reduced_sound hLeaves

/-- Conditional exact BB(6) theorem with the correct 109 residual
    obligations: each retained cylinder is bounded at the champion score,
    not at the earlier classification cutoff 7014. -/
theorem exact_from_reduced_roster_at_champion_score
    (hLeaves : ∀ e ∈ reducedRoster,
      Cover (WeightedBound championScore) e.2) :
    BB6.Coverage.ExactBB6 championScore :=
  BB6.Agent13RosterComposition.exact_from_roster_dichotomy_mixed
    (by decide) (Nat.le_of_lt champion_score_gt_7014) reduced_sound hLeaves champion_raw_witness

#print axioms champion_score_gt_7014
#print axioms champion_compatible_root
#print axioms champion_not_weighted_7014
#print axioms champion_in_reduced_roster
#print axioms champion_singleton_leaf
#print axioms cover_of_reduced_roster_at_champion_score
#print axioms exact_from_reduced_roster_at_champion_score

end BB6.Agent13MixedBound109
