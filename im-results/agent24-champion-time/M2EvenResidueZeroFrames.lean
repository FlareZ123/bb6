import CountedRst1Prime
import M2EvenResidueZeroFinite
import Lean.Elab.Tactic.Omega

/-!
# Full-tape frame lifts for the finite m=2, n=8*k bridge kernels

The finite setup and postlude kernels are exact computations.  These
wrappers lift them to arbitrary infinite tapes using the existing
head-window frame theorem, with no assumption that the surrounding tape
is blank.
-/

namespace BB6Coverage.Agent24M2EvenFrames

open BB6Coverage
open BB6Coverage.Agent8Rst1Prime
open BB6Coverage.Agent8M2EvenResidueZero

/-- Lift the fixed 44-step setup from its exact finite window to any
surrounding tape agreeing with the setup input on [-13,0]. -/
theorem m2ZeroSetup_at (T : Int → Bool) (h : Int)
    (hmatch : ∀ x, m2ZeroSetupInside x = true →
      T (h+x) = decide (x ∈ m2ZeroSetupStart.marked)) :
    run tm2 44 ⟨3,h,T⟩ =
      some (frameAt T h m2ZeroSetupInside m2ZeroSetupEnd) := by
  exact bridgeAt T h m2ZeroSetupInside
    m2ZeroSetupStart m2ZeroSetupEnd 44 rfl
    m2ZeroSetup_exact m2ZeroSetup_heads hmatch

/-- Lift the fixed 14-step postlude from its exact finite window to any
surrounding tape agreeing with thirteen ones followed by a zero. -/
theorem m2ZeroPostlude_at (T : Int → Bool) (h : Int)
    (hmatch : ∀ x, m2ZeroPostludeInside x = true →
      T (h+x) = decide (x ∈ m2ZeroPostludeStart.marked)) :
    run tm2 14 ⟨1,h,T⟩ =
      some (frameAt T h m2ZeroPostludeInside m2ZeroPostludeEnd) := by
  exact bridgeAt T h m2ZeroPostludeInside
    m2ZeroPostludeStart m2ZeroPostludeEnd 14 rfl
    m2ZeroPostlude_exact m2ZeroPostlude_heads hmatch

/-- The setup's output window is exactly zero at its left boundary and
one on the remaining thirteen cells. -/
theorem m2ZeroSetupAt_window (T : Int → Bool) (h : Int)
    (x : Int) (hx : m2ZeroSetupInside x = true) :
    (frameAt T h m2ZeroSetupInside m2ZeroSetupEnd).tape (h+x) =
      decide (x ∈ m2ZeroSetupEnd.marked) := by
  rw [frameAt_tape]
  simp [hx]

/-- The postlude's output window is exactly the finite word
00100100100101. -/
theorem m2ZeroPostludeAt_window (T : Int → Bool) (h : Int)
    (x : Int) (hx : m2ZeroPostludeInside x = true) :
    (frameAt T h m2ZeroPostludeInside m2ZeroPostludeEnd).tape (h+x) =
      decide (x ∈ m2ZeroPostludeEnd.marked) := by
  rw [frameAt_tape]
  simp [hx]

#print axioms m2ZeroSetup_at
#print axioms m2ZeroPostlude_at
#print axioms m2ZeroSetupAt_window
#print axioms m2ZeroPostludeAt_window

end BB6Coverage.Agent24M2EvenFrames
