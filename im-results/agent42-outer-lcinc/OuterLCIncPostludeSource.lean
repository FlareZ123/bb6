import OuterLCIncPostlude
import Lean.Elab.Tactic.Omega

/-!
# Outer LC_Inc: source-frame and suffix facts

This file isolates the exact source-side tape facts needed by the
parameterized postlude. The left sweep, marker frame, and H-run preserve
the far-right source; the S1 physical right word supplies the 111, 00,
counted unary run, and blank exterior.
-/

namespace BB6Coverage.Agent42OuterLCInc

open BB6Coverage
open BB6Coverage.Agent8OuterLCInc
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent24LBinDecHRun
open BB6Coverage.Agent48Champion

/-- Source tape after the initial counted left sweep. -/
def outerLCIncSourceT1 (T : Int → Bool) (h : Int) (a : Nat) :
    Int → Bool :=
  sweptLeft (3*a) T h

/-- Source tape after the finite marker bridge frame. -/
def outerLCIncSourceT2 (T : Int → Bool) (h : Int) (a m : Nat) :
    Int → Bool :=
  (markerBridgeFrameOut m (outerLCIncSourceT1 T h a)
    (h-(3*a:Int))).tape

/-- Source tape after the outer binary H-run. -/
def outerLCIncSourceT3 (T : Int → Bool) (h : Int)
    (a m r : Nat) : Int → Bool :=
  lbinDecHRunTape r (outerLCIncSourceT2 T h a m)
    (outerLCIncH1 h a m)

/-- sideBit ignores an appended suffix before the end of its prefix. -/
theorem outer_sideBit_append_left (xs ys : List Bool) (i : Nat)
    (hi : i < xs.length) :
    sideBit (xs ++ ys) i = sideBit xs i := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simpa [sideBit] using ih i (by simpa using hi)

/-- sideBit enters the appended suffix once the prefix is exhausted. -/
theorem outer_sideBit_append_right (xs ys : List Bool) (i : Nat)
    (hi : xs.length ≤ i) :
    sideBit (xs ++ ys) i = sideBit ys (i-xs.length) := by
  induction xs generalizing i with
  | nil => simp [sideBit]
  | cons x xs ih =>
      cases i with
      | zero => simp at hi
      | succ i =>
          have hi' : xs.length ≤ i := by simp at hi; omega
          simpa [sideBit] using ih ys i hi'

/-- Beyond the end of a finite word, the physical tape is blank. -/
theorem outer_sideBit_false_of_ge_length (xs : List Bool) (i : Nat)
    (hi : xs.length ≤ i) : sideBit xs i = false := by
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih =>
      cases i with
      | zero => simp at hi
      | succ i =>
          have hi' : xs.length ≤ i := by simp at hi; omega
          simpa [sideBit] using ih i hi'

/-- Every cell of a d1-power is one. -/
theorem outer_sideBit_d1pow_true (n i : Nat) (hi : i < 3*n) :
    sideBit (d1pow n) i = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      by_cases hsmall : i < 3
      · interval_cases i <;> simp [d1pow, d1, sideBit]
      · have htail : i-3 < 3*n := by omega
        have hrec := ih (i-3) htail
        have hshift : sideBit (d1pow (n+1)) i =
            sideBit (d1pow n) (i-3) := by
          simp [d1pow, d1, sideBit]
          omega
        rw [hshift]
        exact hrec

/-- The original S1 right suffix has its fixed 111 prefix, then 00,
then exactly b+1 unary triples, and is blank afterwards. -/
theorem outerLCInc_s1_right_facts (L n m a b : Nat) (h : Int) :
    let T := (s1Config L n m a 0 b h).tape
    T (h+2) = true ∧
    T (h+3) = true ∧
    T (h+4) = true ∧
    T (h+5) = false ∧
    T (h+6) = false ∧
    rightOnes T (h+7) (b+1) ∧
    (∀ j : Nat, T (h+3*b+10+j) = false) := by
  dsimp
  have hlen : ([false,true,true,true,false,false] ++ d1pow (b+1)).length =
      3*b+9 := by simp [d1pow_length]
  have hcell (i : Nat) :
      (s1Config L n m a 0 b h).tape (h+1+i) =
        sideBit ([false,true,true,true,false,false] ++ d1pow (b+1)) i := by
    rw [s1Config_right_cell, s1PhysicalRight_source]
  constructor
  · calc
      (s1Config L n m a 0 b h).tape (h+2) =
          (s1Config L n m a 0 b h).tape (h+1+1) := by congr 1 <;> omega
      _ = sideBit ([false,true,true,true,false,false] ++ d1pow (b+1)) 1 :=
        hcell 1
      _ = true := by decide
  constructor
  · calc
      (s1Config L n m a 0 b h).tape (h+3) =
          (s1Config L n m a 0 b h).tape (h+1+2) := by congr 1 <;> omega
      _ = sideBit ([false,true,true,true,false,false] ++ d1pow (b+1)) 2 :=
        hcell 2
      _ = true := by decide
  constructor
  · calc
      (s1Config L n m a 0 b h).tape (h+4) =
          (s1Config L n m a 0 b h).tape (h+1+3) := by congr 1 <;> omega
      _ = sideBit ([false,true,true,true,false,false] ++ d1pow (b+1)) 3 :=
        hcell 3
      _ = true := by decide
  constructor
  · calc
      (s1Config L n m a 0 b h).tape (h+5) =
          (s1Config L n m a 0 b h).tape (h+1+4) := by congr 1 <;> omega
      _ = sideBit ([false,true,true,true,false,false] ++ d1pow (b+1)) 4 :=
        hcell 4
      _ = false := by decide
  constructor
  · calc
      (s1Config L n m a 0 b h).tape (h+6) =
          (s1Config L n m a 0 b h).tape (h+1+5) := by congr 1 <;> omega
      _ = sideBit ([false,true,true,true,false,false] ++ d1pow (b+1)) 5 :=
        hcell 5
      _ = false := by decide
  constructor
  · intro i hi
    have h0 : sideBit (d1pow (b+1)) (3*i) = true :=
      outer_sideBit_d1pow_true (b+1) (3*i) (by omega)
    have h1 : sideBit (d1pow (b+1)) (3*i+1) = true :=
      outer_sideBit_d1pow_true (b+1) (3*i+1) (by omega)
    have h2 : sideBit (d1pow (b+1)) (3*i+2) = true :=
      outer_sideBit_d1pow_true (b+1) (3*i+2) (by omega)
    have hc0 := hcell (6+3*i)
    have hc1 := hcell (7+3*i)
    have hc2 := hcell (8+3*i)
    have hr0 : sideBit ([false,true,true,true,false,false] ++ d1pow (b+1))
        (6+3*i) = sideBit (d1pow (b+1)) (3*i) :=
      outer_sideBit_append_right _ _ _ (by simp)
    have hr1 : sideBit ([false,true,true,true,false,false] ++ d1pow (b+1))
        (7+3*i) = sideBit (d1pow (b+1)) (3*i+1) :=
      outer_sideBit_append_right _ _ _ (by omega)
    have hr2 : sideBit ([false,true,true,true,false,false] ++ d1pow (b+1))
        (8+3*i) = sideBit (d1pow (b+1)) (3*i+2) :=
      outer_sideBit_append_right _ _ _ (by omega)
    refine ⟨?_, ?_, ?_⟩
    · calc
        (s1Config L n m a 0 b h).tape (h+7+3*(i:Int)) =
            (s1Config L n m a 0 b h).tape (h+1+(6+3*i)) := by congr 1 <;> omega
        _ = sideBit ([false,true,true,true,false,false] ++ d1pow (b+1))
            (6+3*i) := hc0
        _ = sideBit (d1pow (b+1)) (3*i) := hr0
        _ = true := h0
    · calc
        (s1Config L n m a 0 b h).tape (h+7+3*(i:Int)+1) =
            (s1Config L n m a 0 b h).tape (h+1+(7+3*i)) := by congr 1 <;> omega
        _ = sideBit ([false,true,true,true,false,false] ++ d1pow (b+1))
            (7+3*i) := hc1
        _ = sideBit (d1pow (b+1)) (3*i+1) := hr1
        _ = true := h1
    · calc
        (s1Config L n m a 0 b h).tape (h+7+3*(i:Int)+2) =
            (s1Config L n m a 0 b h).tape (h+1+(8+3*i)) := by congr 1 <;> omega
        _ = sideBit ([false,true,true,true,false,false] ++ d1pow (b+1))
            (8+3*i) := hc2
        _ = sideBit (d1pow (b+1)) (3*i+2) := hr2
        _ = true := h2
  · intro j
    have hc := hcell (3*b+9+j)
    have hfalse := outer_sideBit_false_of_ge_length
      ([false,true,true,true,false,false] ++ d1pow (b+1))
      (3*b+9+j) (by omega)
    have hcoord : h+3*b+10+(j:Int) = h+1+(3*b+9+j) := by omega
    calc
      (s1Config L n m a 0 b h).tape (h+3*b+10+(j:Int)) =
          (s1Config L n m a 0 b h).tape (h+1+(3*b+9+j)) := by
            congr 1 <;> omega
      _ = sideBit ([false,true,true,true,false,false] ++ d1pow (b+1))
          (3*b+9+j) := hc
      _ = false := hfalse

/-- Pointwise tape equation for the marker bridge frame. -/
theorem markerBridgeFrameOut_tape (m : Nat) (T : Int → Bool)
    (h0 x : Int) :
    (markerBridgeFrameOut m T h0).tape x =
      if markerBridgeInsideAt m h0 x then
        decide (x-h0 ∈ (markerBridgeOutput m).marked)
      else T x := by
  simp [markerBridgeFrameOut, frame, markerBridgeInsideAt,
    shiftConfig, embed]

/-- The marker bridge leaves the five cells for the B-state exit as
four ones followed by one zero. -/
theorem markerBridgeFrameOut_five (m : Nat) (hm : m < 3)
    (T : Int → Bool) (h0 : Int) (j : Nat) (hj : j < 5) :
    (markerBridgeFrameOut m T h0).tape
      (h0-(m+3:Int)+(j:Int)) = decide (j < 4) := by
  have hin : markerBridgeInsideAt m h0
      (h0-(m+3:Int)+(j:Int)) = true := by
    simp [markerBridgeInsideAt, markerBridgeInside]
    omega
  rw [markerBridgeFrameOut_tape]
  simp [hin]
  have hm' : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  rcases hm' with rfl | rfl | rfl <;>
    interval_cases j <;> norm_num [markerBridgeOutput]

/-- The final m marker-frame cells are ones, exactly the prefix
needed at the beginning of the E scan. -/
theorem markerBridgeFrameOut_trailing (m : Nat) (hm : m < 3)
    (T : Int → Bool) (h0 : Int) (i : Nat) (hi : i < m) :
    (markerBridgeFrameOut m T h0).tape
      (h0-(m:Int)+2+(i:Int)) = true := by
  have hin : markerBridgeInsideAt m h0
      (h0-(m:Int)+2+(i:Int)) = true := by
    simp [markerBridgeInsideAt, markerBridgeInside]
    omega
  rw [markerBridgeFrameOut_tape]
  simp [hin]
  have hm' : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  rcases hm' with rfl | rfl | rfl
  · omega
  · interval_cases i <;> norm_num [markerBridgeOutput]
  · interval_cases i <;> norm_num [markerBridgeOutput]

/-- The marker frame preserves every cell strictly to the right of
its fixed output window. -/
theorem markerBridgeFrameOut_preserves_right (m : Nat)
    (T : Int → Bool) (h0 x : Int) (hx : h0+1 < x) :
    (markerBridgeFrameOut m T h0).tape x = T x := by
  rw [markerBridgeFrameOut_tape]
  have hout : markerBridgeInsideAt m h0 x = false := by
    simp [markerBridgeInsideAt, markerBridgeInside]
    omega
  simp [hout]

/-- The complete left-sweep / marker-frame / H-run composition preserves
the original source strictly to the right of h+1. -/
theorem outerLCIncSourceT3_preserves_right
    (T : Int → Bool) (h : Int) (a m r : Nat)
    (x : Int) (hx : h+1 < x) :
    outerLCIncSourceT3 T h a m r x = T x := by
  have hx1 : outerLCIncH1 h a m + 2 ≤ x := by
    dsimp [outerLCIncH1]
    omega
  rw [lbinDecHRunTape_preserves_right r
    (outerLCIncSourceT2 T h a m) (outerLCIncH1 h a m) x hx1]
  rw [markerBridgeFrameOut_preserves_right m
    (outerLCIncSourceT1 T h a) (h-(3*a:Int)) x (by dsimp; omega)]
  exact sweptLeft_preserves_right (3*a) T h x hx


/-- The five-step bridge frame preserves every cell at and beyond the
start of the E scan. -/
theorem outerLCIncAfterFive_preserves_right
    (T : Int → Bool) (h : Int) (a m : Nat) (x : Int)
    (hx : outerLCIncH1 h a m + 7 ≤ x) :
    outerLCIncAfterFive T h a m x = T x := by
  have hnot : outerLCIncFiveInside
      (x-(outerLCIncH1 h a m+2)) = false := by
    simp [outerLCIncFiveInside]
    omega
  simp [outerLCIncAfterFive, frameAt_tape, hnot]

/-- The two-step E-zero frame preserves the B/F/D sweep region. -/
theorem outerLCIncAfterZero_preserves_right
    (T : Int → Bool) (h : Int) (a m : Nat) (x : Int)
    (hx : h+7 ≤ x) :
    outerLCIncAfterZero T h a m x =
      outerLCIncAfterFive T h a m x := by
  have hnot : outerLCIncZeroInside (x-(h+5)) = false := by
    simp [outerLCIncZeroInside]
    omega
  simp [outerLCIncAfterZero, frameAt_tape, hnot]

/-- The two zero-boundary moves write both cells to one. -/
theorem outerLCIncAfterZero_cells
    (T : Int → Bool) (h : Int) (a m : Nat) :
    outerLCIncAfterZero T h a m (h+5) = true ∧
    outerLCIncAfterZero T h a m (h+6) = true := by
  constructor <;>
    simp [outerLCIncAfterZero, frameAt_tape,
      outerLCIncZeroInside, outerLCIncZeroEnd]

/-- The one-step B-zero exit writes one at its current head. -/
theorem outerLCIncAfterZeroExit_one
    (T : Int → Bool) (h : Int) (a m b : Nat) :
    outerLCIncAfterZeroExit T h a m b (h+3*b+10) = true := by
  simp [outerLCIncAfterZeroExit, frameAt_tape,
    outerLCIncZeroExitInside, outerLCIncZeroExitEnd]

/-- Apart from its one written cell, the B-zero exit preserves the
post-sweep tape. -/
theorem outerLCIncAfterZeroExit_preserves
    (T : Int → Bool) (h : Int) (a m b : Nat) (x : Int)
    (hx : x ≠ h+3*b+10) :
    outerLCIncAfterZeroExit T h a m b x =
      outerLCIncAfterSweep T h a m b x := by
  have hnot : outerLCIncZeroExitInside
      (x-(h+3*b+10)) = false := by
    simp [outerLCIncZeroExitInside]
    omega
  simp [outerLCIncAfterZeroExit, frameAt_tape, hnot]


/-- The B/F/D sweep creates the three-cell tail pattern immediately
before and at its last block. The cell at h+3b+6 is the zero-boundary
one when b=0, otherwise the preceding block's third cell. -/
theorem outerLCIncAfterSweep_tailPattern
    (T : Int → Bool) (h : Int) (a m b : Nat)
    (hright : rightOnes (outerLCIncAfterZero T h a m) (h+7) (b+1)) :
    outerLCIncAfterSweep T h a m b (h+3*b+6) = true ∧
    outerLCIncAfterSweep T h a m b (h+3*b+7) = false ∧
    outerLCIncAfterSweep T h a m b (h+3*b+8) = false ∧
    outerLCIncAfterSweep T h a m b (h+3*b+9) = true := by
  have hlast := sweptRightB_block (b+1)
    (outerLCIncAfterZero T h a m) (h+7) hright b (by omega)
  have h6 : outerLCIncAfterSweep T h a m b (h+3*b+6) = true := by
    by_cases hb : b = 0
    · subst b
      have hpres := sweptRightB_preserves_left 1
        (outerLCIncAfterZero T h a m) (h+7) (h+6) (by omega)
      rw [outerLCIncAfterSweep, hpres]
      exact (outerLCIncAfterZero_cells T h a m).2
    · have hpos : 0 < b := by omega
      have hprev := sweptRightB_block (b+1)
        (outerLCIncAfterZero T h a m) (h+7) hright (b-1) (by omega)
      have hcoord : h+3*b+6 =
          h+7+3*((b-1:Int))+2 := by omega
      rw [outerLCIncAfterSweep, hcoord]
      exact hprev.2.2
  refine ⟨h6, ?_, ?_, ?_⟩
  · have hcoord : h+3*b+7 = h+7+3*(b:Int) := by omega
    rw [outerLCIncAfterSweep, hcoord]
    exact hlast.1
  · have hcoord : h+3*b+8 = h+7+3*(b:Int)+1 := by omega
    rw [outerLCIncAfterSweep, hcoord]
    exact hlast.2.1
  · have hcoord : h+3*b+9 = h+7+3*(b:Int)+2 := by omega
    rw [outerLCIncAfterSweep, hcoord]
    exact hlast.2.2

/-- The post-sweep exterior remains blank strictly beyond the final
head of the counted B/F/D sweep. -/
theorem outerLCIncAfterSweep_blank
    (T : Int → Bool) (h : Int) (a m b : Nat) (j : Nat)
    (hblank : ∀ k : Nat, T (h+3*b+10+k) = false)
    (xbound : j ≥ 0) :
    outerLCIncAfterSweep T h a m b (h+3*b+10+j) = false := by
  have hpres := sweptRightB_preserves_right (b+1)
    (outerLCIncAfterZero T h a m) (h+7)
    (h+3*b+10+(j:Int)) (by omega)
  rw [outerLCIncAfterSweep, hpres]
  rw [outerLCIncAfterZero_preserves_right T h a m
    (h+3*b+10+(j:Int)) (by omega)]
  rw [outerLCIncAfterFive_preserves_right T h a m
    (h+3*b+10+(j:Int)) (by dsimp [outerLCIncH1]; omega)]
  rw [outerLCIncSourceT3_preserves_right T h a m
    (Nat.succ rfl) (h+3*b+10+(j:Int)) (by omega)]
  exact hblank j

end BB6Coverage.Agent42OuterLCInc
