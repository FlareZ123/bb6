import RootSourceBridge
import SectionResultRunSource
import TerminalEncoderBridge
import Lean.Elab.Tactic.Omega

/-!
# Three-section root composition of the exact proposed champion score

The original 27959-move root witness enters the first complete SectionResult
section. Two uniform marker-1 resets separate three countdown sections.
The last section has marker 0, so its fully drained output is already in
the source-certified terminal family. This avoids every intermediate
root-specific expansion and special last-decrement/terminal splice.

The only dynamic premises are a uniform counted-increment theorem and a
uniform counted-reset theorem; neither is asserted by this module.
-/

namespace BB6Coverage.Agent48DirectRoot

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent42InitialS1Root
open BB6Coverage.Agent44SectionResultRunSource
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent42TerminalJoin
open BB6ChampionArithmetic

/-- All positive source counters fitting a width at least three. -/
def IncrementSource : Prop :=
  ∀ (L n m a b : Nat) (h : Int),
    3 ≤ L → 0 < n → n < 2^L → 0 < a →
    run tm2 (proposedIncrementCost (m%3) n a b)
      (s1Config L n (m%3) a 0 b h) =
    some (s1Config L (n-1) (nextMarker m) (nextExponent m a b)
      0 (nextRight b) (h+5+3*b))

/-- Complete marker-1 zero-counter reset, with counted drain included. -/
def ResetSource : Prop :=
  ∀ (L a b : Nat) (h : Int),
    run tm2 (resetCost L a b) (s1Config L 0 1 a 0 b h) =
    some (s1Config (L+a+2) (resetIndex L a) 2 b 0 (nextRight b) (h+5+3*b))

private theorem resetIndex_bound (L a : Nat) :
    resetIndex L a < 2^(L+a+2) := by
  rw [resetIndex_eq_pow_sub]
  have hp : 0 < 2^(L+a+2) := Nat.pow_pos (by decide)
  have h := Nat.sub_lt hp (by decide : 0 < 1)
  have hle := Nat.sub_le_sub_right (Nat.sub_le (2^(L+a+2)) (2^a)) 1
  exact Nat.lt_of_le_of_lt hle h

private theorem nextRight_positive (b : Nat) (hb : 0 < b) : 0 < nextRight b := by
  cases b with
  | zero => omega
  | succ b =>
    unfold nextRight
    rw [Nat.pow_succ]
    have hp : 0 < 2^b := Nat.pow_pos (by decide)
    omega

private theorem sectionRight_positive (n m a b : Nat) (hb : 0 < b) :
    0 < (sectionResult n m a b).right := by
  induction n generalizing m a b with
  | zero => exact hb
  | succ n ih =>
    exact ih (nextMarker m) (nextExponent m a b) (nextRight b)
      (nextRight_positive b hb)

private theorem composeRun {n m : Nat} {c d e : Config}
    (h1 : run tm2 n c = some d) (h2 : run tm2 m d = some e) :
    run tm2 (n+m) c = some e := by
  rw [run_add, h1]
  exact h2

/-- The exact primitive cost of three countdown sections and two resets,
    starting from marker 2. -/
def threeSectionMoves (rootSteps L n a b : Nat) : Nat :=
  let f := sectionResult n 2 a b
  let L1 := L+f.exponent+2
  let N1 := resetIndex L f.exponent
  let g := sectionResult N1 2 f.right (nextRight f.right)
  let L2 := L1+g.exponent+2
  let N2 := resetIndex L1 g.exponent
  let j := sectionResult N2 2 g.right (nextRight g.right)
  rootSteps + f.cost + resetCost L f.exponent f.right + g.cost +
    resetCost L1 g.exponent g.right + j.cost + terminalCost L2 j.exponent

/-- Uniform three-section composition. Keeping the initial counter and
    all tape lengths symbolic avoids kernel evaluation of any enormous
    concrete tower in a conversion check. -/
theorem three_section_halts (inc : IncrementSource) (rst : ResetSource)
    (rootSteps L n a b : Nat) (head : Int)
    (hroot : run tm2 rootSteps blank = some (s1Config L n 2 a 0 b head))
    (hL : 3 ≤ L) (hn : n < 2^L) (ha : 0 < a) (hb : 0 < b)
    (hfm : (sectionResult n 2 a b).marker = 1)
    (hgm : (sectionResult (resetIndex L (sectionResult n 2 a b).exponent)
      2 (sectionResult n 2 a b).right (nextRight (sectionResult n 2 a b).right)).marker = 1)
    (hjm : (sectionResult
      (resetIndex (L+(sectionResult n 2 a b).exponent+2)
        (sectionResult (resetIndex L (sectionResult n 2 a b).exponent)
          2 (sectionResult n 2 a b).right (nextRight (sectionResult n 2 a b).right)).exponent)
      2
      (sectionResult (resetIndex L (sectionResult n 2 a b).exponent)
        2 (sectionResult n 2 a b).right (nextRight (sectionResult n 2 a b).right)).right
      (nextRight (sectionResult (resetIndex L (sectionResult n 2 a b).exponent)
        2 (sectionResult n 2 a b).right (nextRight (sectionResult n 2 a b).right)).right)).marker = 0) :
    HaltsAfter championTable (threeSectionMoves rootSteps L n a b + 6) := by
  let f := sectionResult n 2 a b
  let L1 := L+f.exponent+2
  let N1 := resetIndex L f.exponent
  let g := sectionResult N1 2 f.right (nextRight f.right)
  let L2 := L1+g.exponent+2
  let N2 := resetIndex L1 g.exponent
  let j := sectionResult N2 2 g.right (nextRight g.right)
  let h0 : Int := sectionHeadAfter n b head
  let h1 : Int := h0+5+3*f.right
  let h2 : Int := sectionHeadAfter N1 (nextRight f.right) h1
  let h3 : Int := h2+5+3*g.right
  let h4 : Int := sectionHeadAfter N2 (nextRight g.right) h3
  have hfm' : f.marker = 1 := hfm
  have hgm' : g.marker = 1 := hgm
  have hjm' : j.marker = 0 := hjm
  have hL1 : 3 ≤ L1 := by dsimp only [L1]; omega
  have hL2 : 3 ≤ L2 := by dsimp only [L2]; omega
  have hN1 : N1 < 2^L1 := resetIndex_bound L f.exponent
  have hN2 : N2 < 2^L2 := resetIndex_bound L1 g.exponent
  have hfpos : 0 < f.right := sectionRight_positive n 2 a b hb
  have hgpos : 0 < g.right := sectionRight_positive N1 2 f.right
    (nextRight f.right) (nextRight_positive f.right hfpos)
  have first : run tm2 f.cost (s1Config L n 2 a 0 b head) =
      some (s1Config L 0 1 f.exponent 0 f.right h0) := by
    have h := sectionResult_run_of_source_macro L n 2 a b head
      hn ha (fun k m aa bb h hk hbound hpos =>
        inc L k m aa bb h hL hk hbound hpos)
    change run tm2 f.cost (s1Config L n 2 a 0 b head) =
      some (s1Config L 0 f.marker f.exponent 0 f.right h0) at h
    rw [hfm'] at h
    exact h
  have reset1 : run tm2 (resetCost L f.exponent f.right)
      (s1Config L 0 1 f.exponent 0 f.right h0) =
      some (s1Config L1 N1 2 f.right 0 (nextRight f.right) h1) :=
    rst L f.exponent f.right h0
  have middle : run tm2 g.cost
      (s1Config L1 N1 2 f.right 0 (nextRight f.right) h1) =
      some (s1Config L1 0 1 g.exponent 0 g.right h2) := by
    have h := sectionResult_run_of_source_macro L1 N1 2 f.right
      (nextRight f.right) h1 hN1 hfpos (fun n m a b h hn hb ha =>
        inc L1 n m a b h hL1 hn hb ha)
    change run tm2 g.cost (s1Config L1 N1 2 f.right 0 (nextRight f.right) h1) =
      some (s1Config L1 0 g.marker g.exponent 0 g.right h2) at h
    rw [hgm'] at h
    exact h
  have reset2 : run tm2 (resetCost L1 g.exponent g.right)
      (s1Config L1 0 1 g.exponent 0 g.right h2) =
      some (s1Config L2 N2 2 g.right 0 (nextRight g.right) h3) :=
    rst L1 g.exponent g.right h2
  have last : run tm2 j.cost
      (s1Config L2 N2 2 g.right 0 (nextRight g.right) h3) =
      some (s1Config L2 0 0 j.exponent 0 j.right h4) := by
    have h := sectionResult_run_of_source_macro L2 N2 2 g.right
      (nextRight g.right) h3 hN2 hgpos (fun n m a b h hn hb ha =>
        inc L2 n m a b h hL2 hn hb ha)
    change run tm2 j.cost (s1Config L2 N2 2 g.right 0 (nextRight g.right) h3) =
      some (s1Config L2 0 j.marker j.exponent 0 j.right h4) at h
    rw [hjm'] at h
    exact h
  have hprefix := composeRun (composeRun (composeRun (composeRun
    (composeRun hroot first) reset1) middle) reset2) last
  exact champion_halts_after_terminal_prefix
    (rootSteps + f.cost + resetCost L f.exponent f.right + g.cost +
      resetCost L1 g.exponent g.right + j.cost)
    L2 j.exponent _ h4 hprefix (s0_reset_sectionBits L2 j.exponent j.right h4)

theorem three_section_attainment (inc : IncrementSource) (rst : ResetSource)
    (rootSteps L n a b : Nat) (head : Int)
    (hroot : run tm2 rootSteps blank = some (s1Config L n 2 a 0 b head))
    (hL : 3 ≤ L) (hn : n < 2^L) (ha : 0 < a) (hb : 0 < b)
    (hfm : (sectionResult n 2 a b).marker = 1)
    (hgm : (sectionResult (resetIndex L (sectionResult n 2 a b).exponent)
      2 (sectionResult n 2 a b).right (nextRight (sectionResult n 2 a b).right)).marker = 1)
    (hjm : (sectionResult
      (resetIndex (L+(sectionResult n 2 a b).exponent+2)
        (sectionResult (resetIndex L (sectionResult n 2 a b).exponent)
          2 (sectionResult n 2 a b).right (nextRight (sectionResult n 2 a b).right)).exponent)
      2
      (sectionResult (resetIndex L (sectionResult n 2 a b).exponent)
        2 (sectionResult n 2 a b).right (nextRight (sectionResult n 2 a b).right)).right
      (nextRight (sectionResult (resetIndex L (sectionResult n 2 a b).exponent)
        2 (sectionResult n 2 a b).right (nextRight (sectionResult n 2 a b).right)).right)).marker = 0) :
    Attainable (threeSectionMoves rootSteps L n a b + 7) := by
  exact ⟨championTable, threeSectionMoves rootSteps L n a b + 6,
    three_section_halts inc rst rootSteps L n a b head hroot hL hn ha hb hfm hgm hjm, rfl⟩

theorem threeSectionMoves_root : threeSectionMoves 27959 3 7 6 63 = proposedTM63Moves := by
  rfl

theorem direct_root_halts_aux (inc : IncrementSource) (rst : ResetSource) :
    HaltsAfter championTable (threeSectionMoves 27959 3 7 6 63 + 6) := by
  have hm : (sectionResult 7 2 6 63).marker = 1 := by rw [sectionResult_marker]
  exact three_section_halts inc rst 27959 3 7 6 63 29
    tm2_blank_reaches_initialS1_source (by decide) (by decide) (by decide)
    (by decide) hm middle_stage_marker_one final_stage_marker_zero

theorem direct_root_halts (inc : IncrementSource) (rst : ResetSource) :
    HaltsAfter championTable (proposedTM63Moves+6) :=
  Eq.mp (congrArg (HaltsAfter championTable)
    (congrArg (fun n : Nat => n+6) threeSectionMoves_root)) (direct_root_halts_aux inc rst)

theorem direct_root_attainment_aux (inc : IncrementSource) (rst : ResetSource) :
    Attainable (threeSectionMoves 27959 3 7 6 63 + 7) := by
  have hm : (sectionResult 7 2 6 63).marker = 1 := by rw [sectionResult_marker]
  exact three_section_attainment inc rst 27959 3 7 6 63 29
    tm2_blank_reaches_initialS1_source (by decide) (by decide) (by decide)
    (by decide) hm middle_stage_marker_one final_stage_marker_zero

theorem threeSectionScore_root : threeSectionMoves 27959 3 7 6 63 + 7 = proposedTM63Moves + 7 :=
  congrArg (fun n : Nat => n + 7) threeSectionMoves_root

theorem direct_root_attainment (inc : IncrementSource) (rst : ResetSource) :
    Attainable (proposedTM63Moves + 7) :=
  Eq.mp (congrArg Attainable threeSectionScore_root) (direct_root_attainment_aux inc rst)

#print axioms direct_root_halts
#print axioms three_section_attainment
#print axioms direct_root_attainment

end BB6Coverage.Agent48DirectRoot
