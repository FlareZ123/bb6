import ChampionF1OneLDOneRFIntegration
import F0SiblingIntegrationExtended
import Raw139D0LFCover
import Raw139D0LBCover
import Raw139D0LACover

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent6ChampionRaw139D0ThreeIntegration

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent6ChampionResidual
open BB6.Agent13MixedBound109
open BB6.Agent31FourHoleRoster
open BB6.Agent6F0.Integration
open BB6.Agent41F0Extended
open BB6.Agent48F1Integration
open BB6.Agent48F1RFIntegration
open BB6.Agent48F1ZeroLFIntegration
open BB6.Agent6F1OneLAIntegration
open BB6.Agent6F1ZeroRCIntegration
open BB6.Agent6F1OneLDOneRFIntegration

/-- The raw139 parent retains its required A0=1RB initial transition. -/
theorem championResidual_root :
    championResidual initialSlot = some (some ⟨true,true,1⟩) := by
  decide

/-- The source-accepted D0=0LF parent is the depth-three sibling. -/
theorem zeroLF_is_depth3_sibling :
    sameTable BB6.Agent14Raw139D0LF.parent
      (championChild 3 ⟨false,false,5⟩) = true := by
  decide

/-- The source-accepted D0=1LB parent is the depth-three sibling. -/
theorem oneLB_is_depth3_sibling :
    sameTable BB6.Agent14Raw139D0LB.parent
      (championChild 3 ⟨true,false,1⟩) = true := by
  decide

/-- The source-accepted D0=1LA parent is the depth-three sibling. -/
theorem oneLA_is_depth3_sibling :
    sameTable BB6.Agent14Raw139D0LA.parent
      (championChild 3 ⟨true,false,0⟩) = true := by
  decide

theorem zeroLF_parent_present :
    ∃ e ∈ remainingF1OneRF,
      sameTable e.2 BB6.Agent14Raw139D0LF.parent = true := by
  decide

theorem oneLB_parent_present :
    ∃ e ∈ remainingF1OneRF,
      sameTable e.2 BB6.Agent14Raw139D0LB.parent = true := by
  decide

theorem oneLA_parent_present :
    ∃ e ∈ remainingF1OneRF,
      sameTable e.2 BB6.Agent14Raw139D0LA.parent = true := by
  decide

theorem championScore_ge_49394 :
    49394 ≤ championScore := champion_score_ge_49394

theorem cover_zeroLF :
    Cover (WeightedBound championScore) BB6.Agent14Raw139D0LF.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent14Raw139D0LF.all_completions_weighted m hm k d hk hd)
    (Nat.le_trans (by decide : 352 ≤ 49394) championScore_ge_49394)

theorem cover_oneLB :
    Cover (WeightedBound championScore) BB6.Agent14Raw139D0LB.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent14Raw139D0LB.all_completions_weighted m hm k d hk hd)
    (Nat.le_trans (by decide : 7252 ≤ 49394) championScore_ge_49394)

theorem cover_oneLA :
    Cover (WeightedBound championScore) BB6.Agent14Raw139D0LA.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent14Raw139D0LA.all_completions_weighted m hm k d hk hd)
    (Nat.le_trans (by decide : 1361 ≤ 49394) championScore_ge_49394)

def parentZeroLF (p : PartialMachine) : Bool :=
  sameTable p BB6.Agent14Raw139D0LF.parent

def parentOneLB (p : PartialMachine) : Bool :=
  sameTable p BB6.Agent14Raw139D0LB.parent

def parentOneLA (p : PartialMachine) : Bool :=
  sameTable p BB6.Agent14Raw139D0LA.parent

def isD0SourceSibling (p : PartialMachine) : Bool :=
  parentZeroLF p || parentOneLB p || parentOneLA p

/-- The stronger established F1/F0 chain has 104 residuals after the 1LD
    and 1RF source Covers. Remove the three accepted D0 parents exactly. -/
noncomputable def remainingF1D0Three :
    List (List Move × PartialMachine) :=
  remainingF1OneRF.filter (fun e => !isD0SourceSibling e.2)

theorem remainingF1D0Three_count :
    remainingF1D0Three.length = 101 := by
  decide

theorem removedD0Three_count :
    remainingF1OneRF.length - remainingF1D0Three.length = 3 := by
  rw [remainingF1OneRF_count, remainingF1D0Three_count]
  rfl

/-- Every entry of the 104-leaf F1 frontier is either one of the three
    original-source D0 siblings or one of the 101 retained residuals. -/
theorem cover_remainingF1OneRF
    (hLeaves : ∀ e ∈ remainingF1D0Three,
      Cover (WeightedBound championScore) e.2)
    (e : List Move × PartialMachine)
    (he : e ∈ remainingF1OneRF) :
    Cover (WeightedBound championScore) e.2 := by
  by_cases h0 : parentZeroLF e.2 = true
  · have heq : e.2 = BB6.Agent14Raw139D0LF.parent := sameTable_sound h0
    rw [heq]
    exact cover_zeroLF
  · by_cases h1 : parentOneLB e.2 = true
    · have heq : e.2 = BB6.Agent14Raw139D0LB.parent := sameTable_sound h1
      rw [heq]
      exact cover_oneLB
    · by_cases h2 : parentOneLA e.2 = true
      · have heq : e.2 = BB6.Agent14Raw139D0LA.parent := sameTable_sound h2
        rw [heq]
        exact cover_oneLA
      · apply hLeaves e
        apply List.mem_filter.mpr
        exact ⟨he, by simp [isD0SourceSibling, h0, h1, h2]⟩

/-- The 101 residual Covers plus the five previously accepted F1/D0 sibling
    Covers discharge the raw139 champion-containing parent itself. -/
theorem cover_championResidual_from_101_raw139_leaves
    (hLeaves : ∀ e ∈ remainingF1D0Three,
      Cover (WeightedBound championScore) e.2) :
    Cover (WeightedBound championScore) championResidual := by
  have h104 : ∀ e ∈ remainingF1OneRF,
      Cover (WeightedBound championScore) e.2 :=
    fun e he => cover_remainingF1OneRF hLeaves e he
  have h105 : ∀ e ∈ remainingF1OneLD,
      Cover (WeightedBound championScore) e.2 :=
    fun e he => cover_remainingF1OneLD h104 e he
  have h106 : ∀ e ∈ remainingF1ZeroRC,
      Cover (WeightedBound championScore) e.2 :=
    fun e he => cover_remainingF1ZeroRC h105 e he
  have h107 : ∀ e ∈ remainingF1OneLA,
      Cover (WeightedBound championScore) e.2 :=
    fun e he => cover_remainingF1OneLA h106 e he
  have h108 : ∀ e ∈ remainingF1ZeroLF,
      Cover (WeightedBound championScore) e.2 :=
    fun e he => cover_remainingF1ZeroLF h107 e he
  have h109 : ∀ e ∈ remainingF1RF,
      Cover (WeightedBound championScore) e.2 :=
    fun e he => cover_remainingF1RF h108 e he
  have h110 : ∀ e ∈ remainingF1Extended,
      Cover (WeightedBound championScore) e.2 :=
    fun e he => cover_remainingF1Extended h109 e he
  have h112 : ∀ e ∈ remainingExtended,
      Cover (WeightedBound championScore) e.2 :=
    fun e he => cover_remainingExtended h110 e he
  exact BB6.Agent41F0Extended.refined_residual_cover h112

#print axioms championResidual_root
#print axioms zeroLF_is_depth3_sibling
#print axioms oneLB_is_depth3_sibling
#print axioms oneLA_is_depth3_sibling
#print axioms zeroLF_parent_present
#print axioms oneLB_parent_present
#print axioms oneLA_parent_present
#print axioms championScore_ge_49394
#print axioms cover_zeroLF
#print axioms cover_oneLB
#print axioms cover_oneLA
#print axioms remainingF1D0Three_count
#print axioms removedD0Three_count
#print axioms cover_remainingF1OneRF
#print axioms cover_championResidual_from_101_raw139_leaves

end BB6.Agent6ChampionRaw139D0ThreeIntegration
