import ChampionF1ZeroRCIntegration
import ChampionResidualSourceSiblingIntegration
import Raw139SiblingSources
import Raw139D0OneLFCover
import Raw139D0ZeroRCCover
import Raw139D0OneRFCover
import Raw139D0ZeroRACover
import Raw139C1Batch

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent6ChampionRaw139SiblingExtended

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent6ChampionResidual
open BB6.Agent6ChampionRaw139SiblingIntegration
open BB6.Agent6F1ZeroRCIntegration
open BB6.Agent6F1OneLAIntegration
open BB6.Agent48F1ZeroLFIntegration
open BB6.Agent48F1RFIntegration
open BB6.Agent48F1Integration
open BB6.Agent41F0Extended

/-- Four additional independently source-checked F1 siblings omitted from the
    older six-sibling chain: 0RB, 0LA, 1LB, and 1RD. -/
theorem zeroRB_is_depth5_sibling :
    sameTable BB6.Agent41F1ZeroRB.parent
      (championChild 5 ⟨false,true,1⟩) = true := by decide

theorem zeroLA_is_depth5_sibling :
    sameTable BB6.Agent14F1OneLA.parent
      (championChild 5 ⟨false,false,0⟩) = true := by decide

theorem oneLB_is_depth5_sibling :
    sameTable BB6.Agent14F1OneLB.parent
      (championChild 5 ⟨true,false,1⟩) = true := by decide

theorem oneRD_is_depth5_sibling :
    sameTable BB6.Agent14F1OneRD.parent
      (championChild 5 ⟨true,true,3⟩) = true := by decide

theorem zeroRB_parent_present :
    ∃ e ∈ remainingF1ZeroRC,
      sameTable e.2 BB6.Agent41F1ZeroRB.parent = true := by decide

theorem zeroLA_parent_present :
    ∃ e ∈ remainingF1ZeroRC,
      sameTable e.2 BB6.Agent14F1OneLA.parent = true := by decide

theorem oneLB_parent_present :
    ∃ e ∈ remainingF1ZeroRC,
      sameTable e.2 BB6.Agent14F1OneLB.parent = true := by decide

theorem oneRD_parent_present :
    ∃ e ∈ remainingF1ZeroRC,
      sameTable e.2 BB6.Agent14F1OneRD.parent = true := by decide

theorem cover_zeroRB :
    Cover (WeightedBound (proposedTM63Moves + 7))
      BB6.Agent41F1ZeroRB.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent41F1ZeroRB.all_completions_weighted m hm k d hk hd)
    (Nat.le_trans (by decide : 290 ≤ 49394) championScore_ge_49394)

theorem cover_zeroLA :
    Cover (WeightedBound (proposedTM63Moves + 7))
      BB6.Agent14F1OneLA.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent14F1OneLA.all_completions_weighted m hm k d hk hd)
    (Nat.le_trans (by decide : 553 ≤ 49394) championScore_ge_49394)

theorem cover_oneLB :
    Cover (WeightedBound (proposedTM63Moves + 7))
      BB6.Agent14F1OneLB.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent14F1OneLB.all_completions_weighted m hm k d hk hd)
    (Nat.le_trans (by decide : 172 ≤ 49394) championScore_ge_49394)

theorem cover_oneRD :
    Cover (WeightedBound (proposedTM63Moves + 7))
      BB6.Agent14F1OneRD.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent14F1OneRD.all_completions_weighted m hm k d hk hd)
    (Nat.le_trans (by decide : 489 ≤ 49394) championScore_ge_49394)

/-- All nine newly source-accepted sibling parents (five Agent14/D0/F1
    parents plus the four additional F1 parents) have an original-source Cover. -/
/-- Four more source-audited D0 siblings, independent of the three D0
    parents already included above. -/
theorem oneLF_is_depth3_sibling :
    sameTable BB6.Agent14Raw139D0OneLF.parent
      (championChild 3 ⟨true,false,5⟩) = true := by decide

theorem zeroRC_is_depth3_sibling :
    sameTable BB6.Agent14Raw139D0ZeroRC.parent
      (championChild 3 ⟨false,true,2⟩) = true := by decide

theorem oneRF_is_depth3_sibling :
    sameTable BB6.Agent14Raw139D0OneRF.parent
      (championChild 3 ⟨true,true,5⟩) = true := by decide

theorem zeroRA_is_depth3_sibling :
    sameTable BB6.Agent14Raw139D0ZeroRA.parent
      (championChild 3 ⟨false,true,0⟩) = true := by decide

theorem oneLF_parent_present :
    ∃ e ∈ remainingF1ZeroRC,
      sameTable e.2 BB6.Agent14Raw139D0OneLF.parent = true := by decide

theorem zeroRC_parent_present :
    ∃ e ∈ remainingF1ZeroRC,
      sameTable e.2 BB6.Agent14Raw139D0ZeroRC.parent = true := by decide

theorem oneRF_parent_present :
    ∃ e ∈ remainingF1ZeroRC,
      sameTable e.2 BB6.Agent14Raw139D0OneRF.parent = true := by decide

theorem zeroRA_parent_present :
    ∃ e ∈ remainingF1ZeroRC,
      sameTable e.2 BB6.Agent14Raw139D0ZeroRA.parent = true := by decide

theorem cover_oneLF :
    Cover (WeightedBound (proposedTM63Moves + 7))
      BB6.Agent14Raw139D0OneLF.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent14Raw139D0OneLF.all_completions_weighted m hm k d hk hd)
    (Nat.le_trans (by decide : 42038 ≤ 49394) championScore_ge_49394)

theorem cover_zeroRC :
    Cover (WeightedBound (proposedTM63Moves + 7))
      BB6.Agent14Raw139D0ZeroRC.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent14Raw139D0ZeroRC.all_completions_weighted m hm k d hk hd)
    (Nat.le_trans (by decide : 775 ≤ 49394) championScore_ge_49394)

theorem cover_oneRF :
    Cover (WeightedBound (proposedTM63Moves + 7))
      BB6.Agent14Raw139D0OneRF.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent14Raw139D0OneRF.all_completions_weighted m hm k d hk hd)
    (Nat.le_trans (by decide : 6250 ≤ 49394) championScore_ge_49394)

theorem cover_zeroRA :
    Cover (WeightedBound (proposedTM63Moves + 7))
      BB6.Agent14Raw139D0ZeroRA.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent14Raw139D0ZeroRA.all_completions_weighted m hm k d hk hd)
    (Nat.le_trans (by decide : 8840 ≤ 49394) championScore_ge_49394)

def isAdditionalSourceAcceptedSibling (p : PartialMachine) : Bool :=
  isSourceAcceptedSibling p ||
  sameTable p BB6.Agent41F1ZeroRB.parent ||
  sameTable p BB6.Agent14F1OneLA.parent ||
  sameTable p BB6.Agent14F1OneLB.parent ||
  sameTable p BB6.Agent14F1OneRD.parent ||
  sameTable p BB6.Agent14Raw139D0OneLF.parent ||
  sameTable p BB6.Agent14Raw139D0ZeroRC.parent ||
  sameTable p BB6.Agent14Raw139D0OneRF.parent ||
  sameTable p BB6.Agent14Raw139D0ZeroRA.parent

noncomputable def remainingRaw139AfterThirty :
    List (List Move × PartialMachine) :=
  remainingF1ZeroRC.filter
    (fun e => !isAdditionalSourceAcceptedSibling e.2)

theorem remainingRaw139AfterThirty_count :
    remainingRaw139AfterThirty.length = 93 := by decide

theorem removedThirteenSibling_count :
    remainingF1ZeroRC.length - remainingRaw139AfterThirty.length = 13 := by
  rw [remainingF1ZeroRC_count, remainingRaw139AfterThirty_count]
  rfl

theorem additionalSourceAcceptedSiblingCover (p : PartialMachine)
    (hp : isAdditionalSourceAcceptedSibling p = true) :
    Cover (WeightedBound (proposedTM63Moves + 7)) p := by
  by_cases hFive : isSourceAcceptedSibling p = true
  · exact sourceAcceptedSiblingCover p hFive
  · have hFiveFalse : isSourceAcceptedSibling p = false := by
      cases h : isSourceAcceptedSibling p with
      | false => rfl
      | true => exact False.elim (hFive h)
    simp [isAdditionalSourceAcceptedSibling, hFiveFalse] at hp
    rcases hp with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
    · have heq : p = BB6.Agent41F1ZeroRB.parent := sameTable_sound h0
      subst p
      exact cover_zeroRB
    · have heq : p = BB6.Agent14F1OneLA.parent := sameTable_sound h1
      subst p
      exact cover_zeroLA
    · have heq : p = BB6.Agent14F1OneLB.parent := sameTable_sound h2
      subst p
      exact cover_oneLB
    · have heq : p = BB6.Agent14F1OneRD.parent := sameTable_sound h3
      subst p
      exact cover_oneRD
    · have heq : p = BB6.Agent14Raw139D0OneLF.parent := sameTable_sound h4
      subst p
      exact cover_oneLF
    · have heq : p = BB6.Agent14Raw139D0ZeroRC.parent := sameTable_sound h5
      subst p
      exact cover_zeroRC
    · have heq : p = BB6.Agent14Raw139D0OneRF.parent := sameTable_sound h6
      subst p
      exact cover_oneRF
    · have heq : p = BB6.Agent14Raw139D0ZeroRA.parent := sameTable_sound h7
      subst p
      exact cover_zeroRA

theorem cover_remainingF1ZeroRC
    (hLeaves : ∀ e ∈ remainingRaw139AfterThirty,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2)
    (e : List Move × PartialMachine)
    (he : e ∈ remainingF1ZeroRC) :
    Cover (WeightedBound (proposedTM63Moves + 7)) e.2 := by
  by_cases hs : isAdditionalSourceAcceptedSibling e.2 = true
  · exact additionalSourceAcceptedSiblingCover e.2 hs
  · have hFalse : isAdditionalSourceAcceptedSibling e.2 = false := by
      cases h : isAdditionalSourceAcceptedSibling e.2 with
      | false => rfl
      | true => exact False.elim (hs h)
    exact hLeaves e (List.mem_filter.mpr ⟨he, by simp [hFalse]⟩)

/-- Lift the 97 remaining leaves through the already audited F1 and F0
    sibling compositions to a Cover of the retained raw139 parent. -/
theorem cover_championResidual_after_thirty
    (hLeaves : ∀ e ∈ remainingRaw139AfterThirty,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    Cover (WeightedBound (proposedTM63Moves + 7)) championResidual := by
  have h106 : ∀ e ∈ remainingF1ZeroRC,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2 := by
    intro e he
    exact cover_remainingF1ZeroRC hLeaves e he
  have h107 : ∀ e ∈ remainingF1OneLA,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2 :=
    fun e he => cover_remainingF1OneLA h106 e he
  have h108 : ∀ e ∈ remainingF1ZeroLF,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2 :=
    fun e he => cover_remainingF1ZeroLF h107 e he
  have h109 : ∀ e ∈ remainingF1RF,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2 :=
    fun e he => cover_remainingF1RF h108 e he
  have h110 : ∀ e ∈ remainingF1Extended,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2 :=
    fun e he => cover_remainingF1Extended h109 e he
  have h112 : ∀ e ∈ remainingExtended,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2 :=
    fun e he => cover_remainingExtended h110 e he
  exact BB6.Agent41F0Extended.refined_residual_cover h112


/-- The twelve source-audited C1 siblings are distinct from the 30 already
    consumed F0/F1/D0 parents. Match by the finite table comparator, then use
    the source module's exact list-membership consumer. -/
def isC1Sibling (p : PartialMachine) : Bool :=
  BB6.Agent48Raw139C1Batch.parents.any (fun q => sameTable p q)

noncomputable def remainingRaw139AfterFortyTwo :
    List (List Move × PartialMachine) :=
  remainingRaw139AfterThirty.filter (fun e => !isC1Sibling e.2)

theorem c1_parent_count :
    BB6.Agent48Raw139C1Batch.parents.length = 12 := by decide

theorem c1_parents_all_present :
    ∀ p ∈ BB6.Agent48Raw139C1Batch.parents,
      ∃ e ∈ remainingRaw139AfterThirty, sameTable e.2 p = true := by decide

theorem isC1Sibling_false_of_not_mem (p : PartialMachine)
    (hp : p ∉ BB6.Agent48Raw139C1Batch.parents) :
    isC1Sibling p = false := by
  cases h : isC1Sibling p with
  | false => rfl
  | true =>
      have hAny :
          BB6.Agent48Raw139C1Batch.parents.any
            (fun q => sameTable p q) = true := by
        simpa [isC1Sibling] using h
      rcases List.any_eq_true.mp hAny with ⟨q, hq, hSame⟩
      have heq : p = q := sameTable_sound hSame
      exact False.elim (hp (by simpa [heq] using hq))

theorem remainingRaw139AfterFortyTwo_count :
    remainingRaw139AfterFortyTwo.length = 81 := by decide

theorem removedTwelveSibling_count :
    remainingRaw139AfterThirty.length -
      remainingRaw139AfterFortyTwo.length = 12 := by
  rw [remainingRaw139AfterThirty_count,
    remainingRaw139AfterFortyTwo_count]
  rfl

/-- Discharge the twelve C1 parents with the independently source-audited
    2,511 weighted-bound consumer. All other entries remain explicit leaves. -/
theorem cover_remainingRaw139AfterThirty
    (hLeaves : ∀ e ∈ remainingRaw139AfterFortyTwo,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2)
    (e : List Move × PartialMachine)
    (he : e ∈ remainingRaw139AfterThirty) :
    Cover (WeightedBound (proposedTM63Moves + 7)) e.2 := by
  exact BB6.Agent48Raw139C1Batch.consume
    (Nat.le_trans (by decide : 2511 ≤ 49394) championScore_ge_49394)
    remainingRaw139AfterThirty
    (by
      intro x hx hnot
      have hFalse := isC1Sibling_false_of_not_mem x.2 hnot
      exact hLeaves x
        (List.mem_filter.mpr
          ⟨hx, by simp [remainingRaw139AfterFortyTwo, hFalse]⟩))
    e he

/-- The 81 remaining raw139 leaves, plus the 42 already consumed siblings,
    now give a Cover of the champion parent. -/
theorem cover_championResidual_after_fortyTwo
    (hLeaves : ∀ e ∈ remainingRaw139AfterFortyTwo,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    Cover (WeightedBound (proposedTM63Moves + 7)) championResidual := by
  have h93 : ∀ e ∈ remainingRaw139AfterThirty,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2 := by
    intro e he
    exact cover_remainingRaw139AfterThirty hLeaves e he
  exact cover_championResidual_after_thirty h93


#print axioms zeroRB_is_depth5_sibling
#print axioms zeroLA_is_depth5_sibling
#print axioms oneLB_is_depth5_sibling
#print axioms oneLF_is_depth3_sibling
#print axioms zeroRC_is_depth3_sibling
#print axioms oneRF_is_depth3_sibling
#print axioms zeroRA_is_depth3_sibling
#print axioms oneLF_parent_present
#print axioms zeroRC_parent_present
#print axioms oneRF_parent_present
#print axioms zeroRA_parent_present
#print axioms cover_oneLF
#print axioms cover_zeroRC
#print axioms cover_oneRF
#print axioms cover_zeroRA
#print axioms oneRD_is_depth5_sibling
#print axioms zeroRB_parent_present
#print axioms zeroLA_parent_present
#print axioms oneLB_parent_present
#print axioms oneRD_parent_present
#print axioms cover_zeroRB
#print axioms cover_zeroLA
#print axioms cover_oneLB
#print axioms cover_oneRD
#print axioms remainingRaw139AfterThirty_count
#print axioms removedThirteenSibling_count
#print axioms additionalSourceAcceptedSiblingCover
#print axioms cover_remainingF1ZeroRC
#print axioms cover_championResidual_after_thirty
#print axioms c1_parent_count
#print axioms c1_parents_all_present
#print axioms isC1Sibling_false_of_not_mem
#print axioms remainingRaw139AfterFortyTwo_count
#print axioms removedTwelveSibling_count
#print axioms cover_remainingRaw139AfterThirty
#print axioms cover_championResidual_after_fortyTwo

end BB6.Agent6ChampionRaw139SiblingExtended
