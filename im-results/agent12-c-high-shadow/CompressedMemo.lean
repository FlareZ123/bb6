import PurePowerRawParent
import BranchingBlocksSource
import ValuationParents
import DirectJump
import ExactMemo
import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.NativeDecide

set_option maxHeartbeats 4000000

namespace BB6.Agent12CompressedMemo
open BB6.Agent12ValuationParents BB6.Agent12DirectJump BB6.Agent12PureFan
open BB6.Agent13ExactMemo BB6.Agent46
open BB6.Agent42DirectBlocks BB6.Agent42ModularCone BB6.Agent12BranchingBlocks

theorem valuation_length (x y : Nat) :
    (valuationParents x y).length≤v2 (rounded x y)+3 := by
  have h1 := List.length_filterMap_le id [directAt x y,zeroAt x y,oneAt x y]
  have h2 := List.length_filterMap_le (regularAt x y) (List.range (v2 (rounded x y)))
  simp only [List.length_cons,List.length_nil,List.length_range] at h1 h2
  unfold valuationParents
  rw [List.length_append]
  omega

/-- The high-right branch uses only valuations and arithmetic equalities;
    the known exact original enumerator handles all small-right cases. -/
def plainParents (p : BB6.Agent13ExactMemo.P) : List BB6.Agent13ExactMemo.P :=
  if 8≤p.2 then valuationParents p.1 p.2 else sourceParents p

theorem plainParents_mem (p q : BB6.Agent13ExactMemo.P) :
    q∈plainParents p ↔ q∈sourceParents p := by
  unfold plainParents
  split
  next hy =>
    exact (valuationParents_exact q.1 q.2 p.1 p.2 hy).trans
      ((raw_parent_iff q.1 q.2 p.1 p.2 hy).trans
        ((complete_section_inverse q.1 q.2 p.1 p.2 (by omega)).symm.trans
          (BB6.Agent15TotalFast.totalFastCandidates_exact q.1 q.2 p.1 p.2).symm))
  next => rfl

/-- Replace any maximal forced direct prefix by a single exact macro edge.
    Every other node retains all its exact predecessors. -/
def compressedParents (p : BB6.Agent13ExactMemo.P) : List BB6.Agent13ExactMemo.P :=
  if jumpGate p.1 p.2 then [jumpTarget p.1 p.2] else plainParents p

theorem compressedReach_iff (p : BB6.Agent13ExactMemo.P) :
    sourceReach p ↔ p=(5,1) ∨ ∃ q∈compressedParents p, sourceReach q := by
  unfold compressedParents
  split
  next hg =>
    have hj := jump_source BB6.Agent3.CReach BB6.Agent42DirectBlocks.source_direct p.1 p.2 hg
    have hn : p≠(5,1) := by
      intro h
      have hy := hj.2.2
      rw [h] at hy
      omega
    simp only [hn,false_or,List.mem_singleton]
    change BB6.Agent3.CReach p.1 p.2 ↔ ∃ q, q=jumpTarget p.1 p.2 ∧ sourceReach q
    constructor
    · intro hr
      exact ⟨_,rfl,hj.1.mp hr⟩
    · rintro ⟨q,rfl,hq⟩
      exact hj.1.mpr hq
  next hg =>
    rw [sourceReach_iff]
    simp only [plainParents_mem]

theorem compressedRank_lt (p q : BB6.Agent13ExactMemo.P) (h : q∈compressedParents p) :
    sourceRank q<sourceRank p := by
  unfold compressedParents at h
  split at h
  next hg =>
    have hq := List.mem_singleton.mp h
    rw [hq]
    exact jump_rank BB6.Agent3.CReach BB6.Agent42DirectBlocks.source_direct p.1 p.2 hg
  next => exact sourceRank_lt p q ((plainParents_mem p q).mp h)

/-- Sound shortcuts from four independent source-checked certificates.
    A missed shortcut only costs time; it does not discard a predecessor. -/
def enhancedBad (cap : Nat) (p : BB6.Agent13ExactMemo.P) : Bool :=
  sourceBad p || directBlockExcluded p.1 p.2 || branchingBlockExcluded p.1 p.2 ||
    heightExcluded cap p.1 p.2

theorem enhancedBad_sound (cap : Nat) (p : BB6.Agent13ExactMemo.P)
    (h : enhancedBad cap p=true) : ¬sourceReach p := by
  simp only [enhancedBad,Bool.or_eq_true] at h
  rcases h with ((h|h)|h)|h
  · exact sourceBad_sound p h
  · exact BB6.Agent42DirectBlocks.source_directBlockExcluded p.1 p.2 h
  · exact source_branchingBlockExcluded p.1 p.2 h
  · exact source_height_excluded cap p.1 p.2 h

def compressedExcluded (cap f x y : Nat) : Bool :=
  exclude compressedParents (enhancedBad cap) (5,1) f (x,y)

theorem compressedExcluded_sound (cap f x y : Nat)
    (h : compressedExcluded cap f x y=true) : ¬BB6.Agent3.CReach x y :=
  exclude_sound compressedParents (enhancedBad cap) (5,1) sourceReach
    compressedReach_iff (enhancedBad_sound cap) f (x,y) h

def compressedDecision (cap x y : Nat) : Bool :=
  compressedExcluded cap ((x+2*y)/2+1) x y

/-- Complete finite decision, with the same half-weight ranking as the
    established exact memoizer, but much less per-node enumeration. -/
theorem compressedDecision_iff (cap x y : Nat) :
    compressedDecision cap x y=true ↔ ¬BB6.Agent3.CReach x y := by
  constructor
  · exact compressedExcluded_sound cap _ x y
  · intro hn
    exact exclude_complete compressedParents (enhancedBad cap) (5,1) sourceReach sourceRank
      compressedReach_iff (enhancedBad_sound cap) compressedRank_lt _ (x,y) (by simp [sourceRank]) hn

def oldHighSurvives (j m : Nat) : Bool :=
  priorSurvives j m && !highHeightExcluded j m &&
    !directBlockExcluded (2*j+3) (highTarget j m) &&
    !branchingBlockExcluded (2*j+3) (highTarget j m)

theorem oldHighSurvives_iff (j m : Nat) :
    oldHighSurvives j m=true ↔ highAllowedBranching j m := by
  simp only [oldHighSurvives,priorSurvives,Bool.and_eq_true,Bool.not_eq_true',
    decide_eq_true_eq,BB6.Agent27FastBool.fastHighAllowedFullBool_iff,
    highAllowedBranching,highAllowedDirect,highAllowedHeight,highAllowedFullModular,
    ←BB6.Agent27FullBool.highAllowedFullBool_iff,and_assoc]

/-- Bounded additional root guard applicable to any stopping target. -/
def highAllowedMemo (cap f j m : Nat) : Prop :=
  highAllowedBranching j m ∧ compressedExcluded cap f (2*j+3) (highTarget j m)=false

theorem blank_halts_iff_compressed_memo (cap f : Nat) :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowedFullModular m ∧ BB6.Agent3ValSix.valSixMixedRootDecision 1
        (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedMemo cap f j m ∧ BB6.Agent3ValSix.valSixMixedRootDecision
        (2*j+3) (highTarget j m)=true) := by
  rw [blank_halts_iff_branching_blocks]
  constructor
  · rintro (h|⟨j,m,hallow,hroot⟩)
    · exact Or.inl h
    · have hr := (BB6.Agent3ValSix.valSixMixedRootDecision_iff _ _).mp hroot
      have hc : compressedExcluded cap f (2*j+3) (highTarget j m)=false := by
        cases he : compressedExcluded cap f (2*j+3) (highTarget j m) with
        | false => rfl
        | true => exact False.elim ((compressedExcluded_sound _ _ _ _ he) hr)
      exact Or.inr ⟨j,m,⟨hallow,hc⟩,hroot⟩
  · rintro (h|⟨j,m,hallow,hroot⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j,m,hallow.1,hroot⟩


/-- First pure-power high-stop target beyond the existing terminal-mass cutoff.
    The bounded memo result, if true, is a sound exclusion; false is inconclusive. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem highStopSeed_3_2_compressedExcluded :
    compressedExcluded 24 256 986893 7401715 = true := by native_decide

theorem highStopSeed_3_2_not_reachable :
    ¬ BB6.Agent3.CReach 986893 7401715 :=
  compressedExcluded_sound 24 256 986893 7401715 highStopSeed_3_2_compressedExcluded

#print axioms valuation_length
#print axioms plainParents_mem
#print axioms compressedReach_iff
#print axioms compressedRank_lt
#print axioms enhancedBad_sound
#print axioms compressedExcluded_sound
#print axioms compressedDecision_iff
#print axioms oldHighSurvives_iff
#print axioms blank_halts_iff_compressed_memo
#print axioms highStopSeed_3_2_compressedExcluded
#print axioms highStopSeed_3_2_not_reachable


end BB6.Agent12CompressedMemo

