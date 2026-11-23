import OuterLCIncPrelude
import OuterLCIncFiveStep
import OuterLCIncTail
import CountedSweep
import CountedLBinDecHRun
import Lean.Elab.Tactic.Omega

/-!
# Outer LC_Inc: generic parameterized postlude

This module composes the finite five-step marker exit, the E scan, the
two-step zero boundary, the counted B/F/D sweep, the one-step zero exit,
and the fixed 28-step return frame.  It isolates the source-specific
obligations (the relevant one-runs and local frames) from the generic
transition composition.
-/

namespace BB6Coverage.Agent42OuterLCInc

open BB6Coverage
open BB6Coverage.Agent8Rst1Prime
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent24LBinDecHRun

/-- The original head of the outer reset macro. -/
def outerLCIncH1 (h : Int) (a m : Nat) : Int :=
  h - (3*a + m + 5 : Nat)

/-- Tape after the five-step marker exit. -/
def outerLCIncAfterFive (T : Int → Bool) (h : Int) (a m : Nat) :
    Int → Bool :=
  (frameAt T (outerLCIncH1 h a m + 2)
    outerLCIncFiveInside outerLCIncFiveEnd).tape

/-- Tape after the two-step E-zero boundary. -/
def outerLCIncAfterZero (T : Int → Bool) (h : Int) (a m : Nat) :
    Int → Bool :=
  (frameAt (outerLCIncAfterFive T h a m) (h+5)
    outerLCIncZeroInside outerLCIncZeroEnd).tape

/-- Tape after the (b+1) counted B/F/D triples. -/
def outerLCIncAfterSweep (T : Int → Bool) (h : Int)
    (a m b : Nat) : Int → Bool :=
  sweptRightB (b+1) (outerLCIncAfterZero T h a m) (h+7)

/-- Tape after B exits on the zero immediately after the counted run. -/
def outerLCIncAfterZeroExit (T : Int → Bool) (h : Int)
    (a m b : Nat) : Int → Bool :=
  (frameAt (outerLCIncAfterSweep T h a m b) (h+3*b+10)
    outerLCIncZeroExitInside outerLCIncZeroExitEnd).tape

/-- The complete postlude output tape, still expressed as exact source
frames so the final pointwise identification can be proved separately. -/
def outerLCIncPostludeTape (T : Int → Bool) (h : Int)
    (a m b : Nat) : Int → Bool :=
  (frameAt (outerLCIncAfterZeroExit T h a m b) (h+3*b+9)
    outerLCIncTailInside outerLCIncTailEnd).tape

/-- Generic source-level postlude theorem.  The hypotheses are precisely
the local source obligations for each stage; no simulation or finite
parameter enumeration is used. -/
theorem outerLCInc_postlude_run
    (T : Int → Bool) (h : Int) (a m b : Nat)
    (hfive : ∀ x, outerLCIncFiveInside x = true →
      T (outerLCIncH1 h a m + 2 + x) =
        decide (x ∈ outerLCIncFiveStart.marked))
    (hscan : linearRightOnes (outerLCIncAfterFive T h a m)
      (outerLCIncH1 h a m + 7) (3*a+m+3))
    (hzero : (outerLCIncAfterFive T h a m) (h+5) = false ∧
      (outerLCIncAfterFive T h a m) (h+6) = false)
    (hright : rightOnes (outerLCIncAfterZero T h a m)
      (h+7) (b+1))
    (hzeroExit : (outerLCIncAfterSweep T h a m b)
      (h+3*b+10) = false)
    (htail : ∀ x, outerLCIncTailInside x = true →
      (outerLCIncAfterZeroExit T h a m b) (h+3*b+9+x) =
        decide (x ∈ outerLCIncTailStart.marked)) :
    run tm2 (3*a+42+m+3*b) ⟨1,outerLCIncH1 h a m+2,T⟩ =
      some ⟨3,h+3*b+5,outerLCIncPostludeTape T h a m b⟩ := by
  have hfiveRun := outerLCIncFive_at T (outerLCIncH1 h a m+2) hfive
  have hscanRun := E_scan (outerLCIncAfterFive T h a m)
    (outerLCIncH1 h a m+7) (3*a+m+3) hscan
  have hzeroRun := outerLCIncZero_at
    (outerLCIncAfterFive T h a m) (h+5) hzero
  have hrightRun := counted_right_sweep_B (b+1)
    (outerLCIncAfterZero T h a m) (h+7) hright
  have hzeroExitRun := outerLCIncZeroExit_at
    (outerLCIncAfterSweep T h a m b) (h+3*b+10) hzeroExit
  have htailRun := outerLCIncTail_at
    (outerLCIncAfterZeroExit T h a m b) (h+3*b+9) htail
  have hcost :
      3*a+42+m+3*b =
        5 + (3*a+m+3) + 2 + 3*(b+1) + 1 + 28 := by omega
  rw [hcost, run_add, hfiveRun]
  simp only [Option.bind_some]
  rw [run_add, hscanRun]
  simp only [Option.bind_some]
  rw [run_add, hzeroRun]
  simp only [Option.bind_some]
  rw [run_add, hrightRun]
  simp only [Option.bind_some]
  rw [run_add, hzeroExitRun]
  simp only [Option.bind_some]
  exact htailRun

#print axioms outerLCInc_postlude_run

end BB6Coverage.Agent42OuterLCInc
