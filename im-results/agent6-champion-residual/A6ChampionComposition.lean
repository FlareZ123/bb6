import A6Ingestion
import ChampionResidualCanonical77Integration

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent6A6ChampionComposition

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent19HardRoot
open BB6.Agent31FourHoleFrontier
open BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalRefinement
open BB6.Agent50TNFPilot
open BB6.Agent48A6Ingestion
open BB6.Agent6ChampionResidual
open BB6.Agent6F1ZeroRCIntegration
open BB6.Agent6Canonical77ChampionIntegration

/-- The champion's first ordinary refinement of raw139, D/1 = 0LE.
    It is an off-path sibling of the A6 path, whose D/1 move is 0LC. -/
def A6_champion_sibling : PartialMachine :=
  refine championResidual (3, true) (some ⟨false, false, 4⟩)

/-- Remove the champion's first child from the A6 off-path residuals. The
    champion child is handled by the already-developed 106-leaf raw139 chain. -/
noncomputable def A6_remaining_without_champion :
    List (List Move × PartialMachine) :=
  A6_remaining.filter (fun e => !(sameTable e.2 A6_champion_sibling))

/-- Every A6-path residual is either still open, or is the champion's D/1=0LE
    child. In the latter case the 106-leaf champion refinement supplies a
    Cover of the entire parent cylinder. The A6 source theorem closes its
    terminal leaf; its bounded halt siblings lift from 7014 to championScore. -/
theorem A6_remaining_sound_at_championScore
    (hChampionLeaves : ∀ e ∈ remainingF1ZeroRC,
      Cover (WeightedBound championScore) e.2) :
    ∀ m, compatible BB6.Agent19HardRoot.p139 m →
      WeightedBound championScore m ∨
        ∃ e ∈ A6_remaining_without_champion, compatible e.2 m := by
  intro m hm
  rcases A6_remaining_sound m hm with hBound | ⟨e, he, hcomp⟩
  · exact Or.inl (by
      intro k d hk hd
      exact Nat.le_trans (hBound k d hk hd)
        (Nat.le_trans (by decide : 7014 ≤ 49394) champion_score_ge_49394))
  · rcases e with ⟨address, q⟩
    by_cases hSame : sameTable q A6_champion_sibling = true
    · have hq : q = A6_champion_sibling := sameTable_sound hSame
      subst q
      have hChild : compatible
          (refine championResidual (3, true) (some ⟨false, false, 4⟩)) m := by
        simpa [A6_champion_sibling] using hcomp
      have hParentPair :=
        (compatible_refine_iff championResidual m (3, true) (by decide)
          (some ⟨false, false, 4⟩)).mp hChild
      exact Or.inl
        ((cover_championResidual_from_raw139_leaves hChampionLeaves).sound
          m hParentPair.1)
    · exact Or.inr ⟨(address, q),
        List.mem_filter.mpr ⟨he, by simp [hSame]⟩, hcomp⟩

/-- The combined raw139 residual family is the A6 first-hole frontier with
    the champion's D/1=0LE child removed. -/
noncomputable def A6ChampionCombinedRoster :
    List (List Move × PartialMachine) :=
  graftRoster BB6.Agent19HardRoot.p139 A6_remaining_without_champion
    BB6.Agent47CanonicalRaw114Accepted.roster

/-- The 77-entry accepted canonical root dichotomy, lifted to the attained
    champion score, then grafted with the combined raw139 residual family. -/
theorem A6ChampionCombinedRoster_sound
    (hChampionLeaves : ∀ e ∈ remainingF1ZeroRC,
      Cover (WeightedBound championScore) e.2) :
    ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound championScore m ∨
        ∃ e ∈ A6ChampionCombinedRoster, TNFQuotientCompatible e.2 m := by
  have hRoot :
      ∀ m, compatible BB6.Agent50TNFPilot.root m →
        WeightedBound championScore m ∨
          ∃ e ∈ BB6.Agent47CanonicalRaw114Accepted.roster,
            TNFQuotientCompatible e.2 m := by
    intro m hm
    rcases BB6.Agent47CanonicalRaw114Accepted.sound m hm with hBound | hResidual
    · exact Or.inl (by
        intro k d hk hd
        exact Nat.le_trans (hBound k d hk hd)
          (Nat.le_trans (by decide : 7014 ≤ 49394) champion_score_ge_49394))
    · exact Or.inr hResidual
  exact graftRoster_sound (RawRootPath.rootRow p139_rawRootPath)
    hRoot (A6_remaining_sound_at_championScore hChampionLeaves)

/-- The A6 and champion subfrontiers together produce a genuine Cover of
    raw139, conditional only on Covers for the 183 retained A6 siblings and
    the 106 champion descendants. -/
theorem combined_A6_parent_cover
    (hA6Leaves : ∀ e ∈ A6_remaining_without_champion,
      Cover (WeightedBound championScore) e.2)
    (hChampionLeaves : ∀ e ∈ remainingF1ZeroRC,
      Cover (WeightedBound championScore) e.2) :
    Cover (WeightedBound championScore) BB6.Agent19HardRoot.p139 := by
  refine Cover.leaf _ ?_
  intro m hm
  rcases A6_remaining_sound_at_championScore hChampionLeaves m hm with
    hBound | ⟨e, he, hcomp⟩
  · exact hBound
  · exact (hA6Leaves e he).sound m hcomp

/-- Conditional exact BB(6) after composing the source-certified A6 D/1=0LC
    leaf with the champion D/1=0LE refinement. The 77-roster parent entry is
    replaced by the combined raw139 proof; every other canonical entry remains
    an explicit Cover obligation. -/
theorem exact_from_canonical77_with_A6_champion_refinement
    (hOther : ∀ e ∈ BB6.Agent47CanonicalRaw114Accepted.roster,
      e.2 ≠ BB6.Agent19HardRoot.p139 →
        Cover (WeightedBound championScore) e.2)
    (hA6Leaves : ∀ e ∈ A6_remaining_without_champion,
      Cover (WeightedBound championScore) e.2)
    (hChampionLeaves : ∀ e ∈ remainingF1ZeroRC,
      Cover (WeightedBound championScore) e.2) :
    BB6.Coverage.ExactBB6 championScore := by
  have hParentCover :=
    combined_A6_parent_cover hA6Leaves hChampionLeaves
  exact BB6.Agent47CanonicalRaw114Accepted.exact_at_target championScore
    (Nat.le_trans (by decide : 7014 ≤ 49394) champion_score_ge_49394)
    (by
      intro e he
      by_cases hSame : sameTable e.2 BB6.Agent19HardRoot.p139 = true
      · have heq : e.2 = BB6.Agent19HardRoot.p139 := sameTable_sound hSame
        rw [heq]
        exact hParentCover
      · have hne : e.2 ≠ BB6.Agent19HardRoot.p139 := by
          intro hEq
          have hself :
              sameTable BB6.Agent19HardRoot.p139
                BB6.Agent19HardRoot.p139 = true := by decide
          exact hSame (by simpa [hEq] using hself)
        exact hOther e he hne)
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms A6_remaining_sound_at_championScore
#print axioms A6ChampionCombinedRoster_sound
#print axioms combined_A6_parent_cover
#print axioms exact_from_canonical77_with_A6_champion_refinement

end BB6.Agent6A6ChampionComposition
