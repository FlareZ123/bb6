import ChampionResidualParentIntegration
import Agent14OneLDCover
import Agent14OneRFCover
import Raw139D0LFCover
import Raw139D0LBCover
import Raw139D0LACover

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent6ChampionRaw139SiblingIntegration

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent6ChampionResidual
open BB6.Agent31ChampionParentIntegration
open BB6.Agent31FourHoleRoster
open BB6.Agent13MixedBound109

/-- The accepted D0=0LF cylinder is the ordinary D/0 sibling at depth 3. -/
theorem zeroLF_is_depth3_sibling :
    sameTable BB6.Agent14Raw139D0LF.parent
      (championChild 3 ⟨false,false,5⟩) = true := by
  decide

/-- The accepted D0=1LB cylinder is the ordinary D/0 sibling at depth 3. -/
theorem oneLB_is_depth3_sibling :
    sameTable BB6.Agent14Raw139D0LB.parent
      (championChild 3 ⟨true,false,1⟩) = true := by
  decide

/-- The accepted D0=1LA cylinder is the ordinary D/0 sibling at depth 3. -/
theorem oneLA_is_depth3_sibling :
    sameTable BB6.Agent14Raw139D0LA.parent
      (championChild 3 ⟨true,false,0⟩) = true := by
  decide

/-- The accepted F1=1LD cylinder is the ordinary F/1 sibling at depth 5. -/
theorem oneLD_is_depth5_sibling :
    sameTable BB6.Agent14F1OneLD.parent
      (championChild 5 ⟨true,false,3⟩) = true := by
  decide

/-- The accepted F1=1RF cylinder is the ordinary F/1 sibling at depth 5. -/
theorem oneRF_is_depth5_sibling :
    sameTable BB6.Agent14F1OneRF.parent
      (championChild 5 ⟨true,true,5⟩) = true := by
  decide

/-- All five source-accepted sibling parents occur in the explicit 123-leaf
    parent-refined frontier, not merely in a label-derived candidate list. -/
theorem zeroLF_parent_present :
    ∃ e ∈ championResidualFrontierWithParentResiduals,
      sameTable e.2 BB6.Agent14Raw139D0LF.parent = true := by
  decide

theorem oneLB_parent_present :
    ∃ e ∈ championResidualFrontierWithParentResiduals,
      sameTable e.2 BB6.Agent14Raw139D0LB.parent = true := by
  decide

theorem oneLA_parent_present :
    ∃ e ∈ championResidualFrontierWithParentResiduals,
      sameTable e.2 BB6.Agent14Raw139D0LA.parent = true := by
  decide

theorem oneLD_parent_present :
    ∃ e ∈ championResidualFrontierWithParentResiduals,
      sameTable e.2 BB6.Agent14F1OneLD.parent = true := by
  decide

theorem oneRF_parent_present :
    ∃ e ∈ championResidualFrontierWithParentResiduals,
      sameTable e.2 BB6.Agent14F1OneRF.parent = true := by
  decide

/-- The champion score is already above every one of these five local bounds. -/
theorem championScore_ge_7015 :
    7015 ≤ proposedTM63Moves + 7 :=
  Nat.le_of_lt (by
    simpa [BB6.Agent13MixedBound109.championScore] using
      BB6.Agent31Canonical78Exact.champion_score_gt_7014)

theorem cover_zeroLF :
    Cover (WeightedBound (proposedTM63Moves + 7))
      BB6.Agent14Raw139D0LF.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent14Raw139D0LF.all_completions_weighted m hm k d hk hd)
    (Nat.le_trans (by decide : 352 ≤ 7015) championScore_ge_7015)

theorem cover_oneLB :
    Cover (WeightedBound (proposedTM63Moves + 7))
      BB6.Agent14Raw139D0LB.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent14Raw139D0LB.all_completions_weighted m hm k d hk hd)
    (Nat.le_trans (by decide : 7252 ≤ 7015) championScore_ge_7015)

theorem cover_oneLA :
    Cover (WeightedBound (proposedTM63Moves + 7))
      BB6.Agent14Raw139D0LA.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent14Raw139D0LA.all_completions_weighted m hm k d hk hd)
    (Nat.le_trans (by decide : 1361 ≤ 7015) championScore_ge_7015)

theorem cover_oneLD :
    Cover (WeightedBound (proposedTM63Moves + 7))
      BB6.Agent14F1OneLD.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent14F1OneLD.all_completions_weighted m hm k d hk hd)
    (Nat.le_trans (by decide : 264 ≤ 7015) championScore_ge_7015)

theorem cover_oneRF :
    Cover (WeightedBound (proposedTM63Moves + 7))
      BB6.Agent14F1OneRF.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent14F1OneRF.all_completions_weighted m hm k d hk hd)
    (Nat.le_trans (by decide : 5423 ≤ 7015) championScore_ge_7015)

/-- Exactly the five independently source-accepted raw139 siblings are
    removed from the 123-leaf frontier. -/
def isSourceAcceptedSibling (p : PartialMachine) : Bool :=
  sameTable p BB6.Agent14Raw139D0LF.parent ||
  sameTable p BB6.Agent14Raw139D0LB.parent ||
  sameTable p BB6.Agent14Raw139D0LA.parent ||
  sameTable p BB6.Agent14F1OneLD.parent ||
  sameTable p BB6.Agent14F1OneRF.parent

noncomputable def remainingRaw139AfterFive :
    List (List Move × PartialMachine) :=
  championResidualFrontierWithParentResiduals.filter
    (fun e => !isSourceAcceptedSibling e.2)

theorem remainingRaw139AfterFive_count :
    remainingRaw139AfterFive.length = 118 := by
  decide

theorem removedFiveSibling_count :
    championResidualFrontierWithParentResiduals.length -
      remainingRaw139AfterFive.length = 5 := by
  rw [championResidualFrontierWithParentCount, remainingRaw139AfterFive_count]
  rfl

/-- Every parent selected by the exact-table filter has an original-source
    Cover at the champion score. -/
theorem sourceAcceptedSiblingCover (p : PartialMachine)
    (hp : isSourceAcceptedSibling p = true) :
    Cover (WeightedBound (proposedTM63Moves + 7)) p := by
  simp [isSourceAcceptedSibling] at hp
  rcases hp with h0 | h1 | h2 | h3 | h4
  · have heq : p = BB6.Agent14Raw139D0LF.parent := sameTable_sound h0
    subst p
    exact cover_zeroLF
  · have heq : p = BB6.Agent14Raw139D0LB.parent := sameTable_sound h1
    subst p
    exact cover_oneLB
  · have heq : p = BB6.Agent14Raw139D0LA.parent := sameTable_sound h2
    subst p
    exact cover_oneLA
  · have heq : p = BB6.Agent14F1OneLD.parent := sameTable_sound h3
    subst p
    exact cover_oneLD
  · have heq : p = BB6.Agent14F1OneRF.parent := sameTable_sound h4
    subst p
    exact cover_oneRF

/-- The 123-leaf parent frontier is covered by five source certificates plus
    118 remaining explicit residual obligations. -/
theorem cover_remainingRaw139Frontier
    (hLeaves : ∀ e ∈ remainingRaw139AfterFive,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2)
    (e : List Move × PartialMachine)
    (he : e ∈ championResidualFrontierWithParentResiduals) :
    Cover (WeightedBound (proposedTM63Moves + 7)) e.2 := by
  by_cases hs : isSourceAcceptedSibling e.2 = true
  · exact sourceAcceptedSiblingCover e.2 hs
  · apply hLeaves e
    exact List.mem_filter.mpr ⟨he, by simp [hs]⟩

/-- The raw139 parent graft now leaves 77 non-champion canonical obligations
    and 118 explicit raw139 residual Covers. -/
theorem canonical78_refined_obligation_count :
    (BB6.Agent47Canonical78.roster.filter
      (fun e => e.1 ≠ championResidualAddress)).length +
      remainingRaw139AfterFive.length = 195 := by
  rw [canonical78_other_address_count, remainingRaw139AfterFive_count]
  rfl

/-- Conditional global exactness after five original-source sibling Covers.
    The 77 other canonical Covers and 118 residual Covers remain premises. -/
theorem exact_from_remainingRaw139AfterFive
    (hOther : ∀ e ∈ BB6.Agent47Canonical78.roster,
      e.2 ≠ championResidual →
        Cover (WeightedBound (proposedTM63Moves + 7)) e.2)
    (hLeaves : ∀ e ∈ remainingRaw139AfterFive,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_from_nonchampion_roster_covers_and_parent_frontier hOther
    (fun e he => cover_remainingRaw139Frontier hLeaves e he)

#print axioms BB6.Agent14Raw139D0LF.all_completions_weighted
#print axioms BB6.Agent14Raw139D0LB.all_completions_weighted
#print axioms BB6.Agent14Raw139D0LA.all_completions_weighted
#print axioms BB6.Agent14F1OneLD.all_completions_weighted
#print axioms BB6.Agent14F1OneRF.all_completions_weighted
#print axioms zeroLF_is_depth3_sibling
#print axioms oneLB_is_depth3_sibling
#print axioms oneLA_is_depth3_sibling
#print axioms oneLD_is_depth5_sibling
#print axioms oneRF_is_depth5_sibling
#print axioms zeroLF_parent_present
#print axioms oneLB_parent_present
#print axioms oneLA_parent_present
#print axioms oneLD_parent_present
#print axioms oneRF_parent_present
#print axioms cover_zeroLF
#print axioms cover_oneLB
#print axioms cover_oneLA
#print axioms cover_oneLD
#print axioms cover_oneRF
#print axioms remainingRaw139AfterFive_count
#print axioms removedFiveSibling_count
#print axioms sourceAcceptedSiblingCover
#print axioms cover_remainingRaw139Frontier
#print axioms canonical78_refined_obligation_count
#print axioms exact_from_remainingRaw139AfterFive

end BB6.Agent6ChampionRaw139SiblingIntegration
