import Lean
import CountedReset
import ResetBaseFrames
import CountedOddBase
import CountedOneZeroUnary

namespace BB6Coverage.Agent8CountedReset

open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder

/-
A finite, source-authentic base family for the Rst0/Rst1/Rst2 pre-drain
prefix.  These are local framed traces for the a=b=0, odd-outer-counter
boundary pattern.  The surrounding infinite tape is arbitrary outside the
indicated interval.  This file does NOT yet identify the local frames with
all S1 source configurations; that embedding and the a,b,v₂ extensions
remain the universal-prefix proof gap.
-/

/-- Exact finite TM63 trace for all three marker base cases. -/
theorem resetBase_exact (m : Nat) (hm : m < 3) :
    fRun tm2 (63 + 4*m) (resetBaseInput m) =
      some (resetBaseOutput m) := by
  have hcases : m=0 ∨ m=1 ∨ m=2 := by omega
  rcases hcases with h|h|h
  · subst m
    native_decide
  · subst m
    native_decide
  · subst m
    native_decide

/-- The local odd-base trace length agrees with the candidate reset-prefix
cost at n=1, a=b=0. -/
theorem resetBase_cost_eq (m : Nat) :
    63 + 4*m = resetPrefixCost m 1 0 0 := by
  have hv : BB6ChampionArithmetic.v2 1 = 0 := v2_of_odd 1 (by decide)
  simp [resetPrefixCost,hv]

/-- In the b=0 base cases the source head advances exactly five cells. -/
theorem resetBase_head_shift (m : Nat) (hm : m < 3) :
    (resetBaseOutput m).head = (resetBaseInput m).head + 5 := by
  have hcases : m=0 ∨ m=1 ∨ m=2 := by omega
  rcases hcases with h|h|h
  · subst m
    rfl
  · subst m
    rfl
  · subst m
    rfl

/-- The base traces never query outside their local frame intervals. -/
theorem resetBase_heads (m : Nat) (hm : m < 3) :
    ∀ k, k < 63 + 4*m → ∀ d,
      run tm2 k (embed (resetBaseInput m)) = some d →
      resetBaseInside m d.head = true := by
  have hcheck :
      (List.range (63 + 4*m)).all (fun k =>
        match fRun tm2 k (resetBaseInput m) with
        | none => true
        | some f => resetBaseInside m f.head) = true := by
    have hcases : m=0 ∨ m=1 ∨ m=2 := by omega
    rcases hcases with h|h|h
    · subst m
      native_decide
    · subst m
      native_decide
    · subst m
      native_decide
  exact even_finite_heads tm2 (resetBaseInside m) (resetBaseInput m)
    (63 + 4*m) hcheck

/-- Arbitrary exterior bits are preserved: these are exact source-machine
runs of 63, 67, or 71 steps on the corresponding local Rst base frame. -/
theorem resetBase_frame (m : Nat) (hm : m < 3)
    (background : Int → Bool) :
    run tm2 (63 + 4*m)
      (frame (resetBaseInside m) background (embed (resetBaseInput m))) =
      some (frame (resetBaseInside m) background (embed (resetBaseOutput m))) := by
  rw [run_frame tm2 (resetBaseInside m) background
    (embed (resetBaseInput m)) (63 + 4*m) (resetBase_heads m hm)]
  rw [← finite_run_source tm2 (63 + 4*m) (resetBaseInput m)]
  rw [resetBase_exact m hm]
  rfl

#print axioms resetBase_exact
#print axioms resetBase_heads
#print axioms resetBase_frame

end BB6Coverage.Agent8CountedReset
