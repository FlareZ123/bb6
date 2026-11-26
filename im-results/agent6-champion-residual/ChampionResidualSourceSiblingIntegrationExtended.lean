import ChampionF1ZeroRCIntegration
import ChampionResidualSourceSiblingIntegration
import Raw139SiblingSources
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
def isAdditionalSourceAcceptedSibling (p : PartialMachine) : Bool :=
  isSourceAcceptedSibling p ||
  sameTable p BB6.Agent41F1ZeroRB.parent ||
  sameTable p BB6.Agent14F1OneLA.parent ||
  sameTable p BB6.Agent14F1OneLB.parent ||
  sameTable p BB6.Agent14F1OneRD.parent

noncomputable def remainingRaw139AfterTwentySix :
    List (List Move × PartialMachine) :=
  remainingF1ZeroRC.filter
    (fun e => !isAdditionalSourceAcceptedSibling e.2)

theorem remainingRaw139AfterTwentySix_count :
    remainingRaw139AfterTwentySix.length = 97 := by decide

theorem removedNineSibling_count :
    remainingF1ZeroRC.length - remainingRaw139AfterTwentySix.length = 9 := by
  rw [remainingF1ZeroRC_count, remainingRaw139AfterTwentySix_count]
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
    rcases hp with h0 | h1 | h2 | h3
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

theorem cover_remainingF1ZeroRC
    (hLeaves : ∀ e ∈ remainingRaw139AfterTwentySix,
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
theorem cover_championResidual_after_twentySix
    (hLeaves : ∀ e ∈ remainingRaw139AfterTwentySix,
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


/-- The twelve source-audited C1 siblings are distinct from the 26 already
    consumed F0/F1/D0 parents. Match by the finite table comparator, then use
    the source module's exact list-membership consumer. -/
def isC1Sibling (p : PartialMachine) : Bool :=
  BB6.Agent48Raw139C1Batch.parents.any (fun q => sameTable p q)

noncomputable def remainingRaw139AfterThirtyEight :
    List (List Move × PartialMachine) :=
  remainingRaw139AfterTwentySix.filter (fun e => !isC1Sibling e.2)

theorem c1_parent_count :
    BB6.Agent48Raw139C1Batch.parents.length = 12 := by decide

theorem c1_parents_all_present :
    ∀ p ∈ BB6.Agent48Raw139C1Batch.parents,
      ∃ e ∈ remainingRaw139AfterTwentySix, sameTable e.2 p = true := by decide

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

theorem remainingRaw139AfterThirtyEight_count :
    remainingRaw139AfterThirtyEight.length = 85 := by decide

theorem removedTwelveSibling_count :
    remainingRaw139AfterTwentySix.length -
      remainingRaw139AfterThirtyEight.length = 12 := by
  rw [remainingRaw139AfterTwentySix_count,
    remainingRaw139AfterThirtyEight_count]
  rfl

/-- Discharge the twelve C1 parents with the independently source-audited
    2,511 weighted-bound consumer. All other entries remain explicit leaves. -/
theorem cover_remainingRaw139AfterTwentySix
    (hLeaves : ∀ e ∈ remainingRaw139AfterThirtyEight,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2)
    (e : List Move × PartialMachine)
    (he : e ∈ remainingRaw139AfterTwentySix) :
    Cover (WeightedBound (proposedTM63Moves + 7)) e.2 := by
  exact BB6.Agent48Raw139C1Batch.consume
    (Nat.le_trans (by decide : 2511 ≤ 49394) championScore_ge_49394)
    remainingRaw139AfterTwentySix
    (by
      intro x hx hnot
      have hFalse := isC1Sibling_false_of_not_mem x.2 hnot
      exact hLeaves x
        (List.mem_filter.mpr
          ⟨hx, by simp [remainingRaw139AfterThirtyEight, hFalse]⟩))
    e he

/-- The 85 remaining raw139 leaves, plus the 26 already consumed siblings,
    now give a Cover of the champion parent. -/
theorem cover_championResidual_after_thirtyEight
    (hLeaves : ∀ e ∈ remainingRaw139AfterThirtyEight,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    Cover (WeightedBound (proposedTM63Moves + 7)) championResidual := by
  have h97 : ∀ e ∈ remainingRaw139AfterTwentySix,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2 := by
    intro e he
    exact cover_remainingRaw139AfterTwentySix hLeaves e he
  exact cover_championResidual_after_twentySix h97


#print axioms zeroRB_is_depth5_sibling
#print axioms zeroLA_is_depth5_sibling
#print axioms oneLB_is_depth5_sibling
#print axioms oneRD_is_depth5_sibling
#print axioms zeroRB_parent_present
#print axioms zeroLA_parent_present
#print axioms oneLB_parent_present
#print axioms oneRD_parent_present
#print axioms cover_zeroRB
#print axioms cover_zeroLA
#print axioms cover_oneLB
#print axioms cover_oneRD
#print axioms remainingRaw139AfterTwentySix_count
#print axioms removedNineSibling_count
#print axioms additionalSourceAcceptedSiblingCover
#print axioms cover_remainingF1ZeroRC
#print axioms cover_championResidual_after_twentySix
#print axioms c1_parent_count
#print axioms c1_parents_all_present
#print axioms isC1Sibling_false_of_not_mem
#print axioms remainingRaw139AfterThirtyEight_count
#print axioms removedTwelveSibling_count
#print axioms cover_remainingRaw139AfterTwentySix
#print axioms cover_championResidual_after_thirtyEight

end BB6.Agent6ChampionRaw139SiblingExtended
