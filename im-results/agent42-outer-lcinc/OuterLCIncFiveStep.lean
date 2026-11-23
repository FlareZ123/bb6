import CountedRst1Prime
import ChampionRootBridge
import Lean.Elab.Tactic.Omega

/-!
# Outer LC_Inc: five-step marker exit

From the B-state H-run endpoint, the next five original TM63 moves cross
four consecutive ones and the following zero.  This finite kernel is
lifted to arbitrary tape backgrounds; its input is the right edge of the
three-case marker bridge output.
-/

namespace BB6Coverage.Agent42OuterLCInc

open BB6Coverage
open BB6Coverage.Agent8Rst1Prime
open BB6Coverage.Agent48Champion

/-- The five-step exit reads/writes exactly offsets 0 through 4. -/
def outerLCIncFiveInside (x : Int) : Bool :=
  decide (0 ≤ x ∧ x ≤ 4)

/-- B at the first of four ones. -/
def outerLCIncFiveStart : FConfig :=
  ⟨1, 0, [0, 1, 2, 3]⟩

/-- E at the zero just after the four ones, with the two cells
rewritten by the finite trace recorded explicitly. -/
def outerLCIncFiveEnd : FConfig :=
  ⟨4, 5, [4, 2]⟩

theorem outerLCIncFive_exact :
    fRun tm2 5 outerLCIncFiveStart = some outerLCIncFiveEnd := by
  decide

theorem outerLCIncFive_heads :
    (List.range 5).all (fun k =>
      match fRun tm2 k outerLCIncFiveStart with
      | none => true
      | some c => outerLCIncFiveInside c.head) = true := by
  decide

/-- Arbitrary-background lift of the five-step marker exit. -/
theorem outerLCIncFive_at (T : Int → Bool) (h : Int)
    (hmatch : ∀ x, outerLCIncFiveInside x = true →
      T (h+x) = decide (x ∈ outerLCIncFiveStart.marked)) :
    run tm2 5 ⟨1,h,T⟩ =
      some (frameAt T h outerLCIncFiveInside outerLCIncFiveEnd) := by
  exact bridgeAt T h outerLCIncFiveInside
    outerLCIncFiveStart outerLCIncFiveEnd 5 rfl
    outerLCIncFive_exact outerLCIncFive_heads hmatch

#print axioms outerLCIncFive_exact
#print axioms outerLCIncFive_at


/-! ## Two-step zero boundary -/

/-- The zero boundary reads and writes offsets 0 and 1. -/
def outerLCIncZeroInside (x : Int) : Bool :=
  decide (0 ≤ x ∧ x ≤ 1)

/-- E at a zero followed by A at a zero. -/
def outerLCIncZeroStart : FConfig :=
  ⟨4, 0, []⟩

/-- B two cells to the right, with both zero cells now one. -/
def outerLCIncZeroEnd : FConfig :=
  ⟨1, 2, [1, 0]⟩

theorem outerLCIncZero_exact :
    fRun tm2 2 outerLCIncZeroStart = some outerLCIncZeroEnd := by
  decide

theorem outerLCIncZero_heads :
    (List.range 2).all (fun k =>
      match fRun tm2 k outerLCIncZeroStart with
      | none => true
      | some c => outerLCIncZeroInside c.head) = true := by
  decide

/-- Arbitrary-background lift of the two-step zero boundary. -/
theorem outerLCIncZero_at (T : Int → Bool) (h : Int)
    (hmatch : ∀ x, outerLCIncZeroInside x = true →
      T (h+x) = decide (x ∈ outerLCIncZeroStart.marked)) :
    run tm2 2 ⟨4,h,T⟩ =
      some (frameAt T h outerLCIncZeroInside outerLCIncZeroEnd) := by
  exact bridgeAt T h outerLCIncZeroInside
    outerLCIncZeroStart outerLCIncZeroEnd 2 rfl
    outerLCIncZero_exact outerLCIncZero_heads hmatch

#print axioms outerLCIncZero_exact
#print axioms outerLCIncZero_at


/-! ## One-step B-zero exit -/

/-- The zero exit touches only its current cell. -/
def outerLCIncZeroExitInside (x : Int) : Bool :=
  decide (x = 0)

/-- B on zero writes one and moves left into state C. -/
def outerLCIncZeroExitStart : FConfig :=
  ⟨1, 0, []⟩

def outerLCIncZeroExitEnd : FConfig :=
  ⟨2, -1, [0]⟩

theorem outerLCIncZeroExit_exact :
    fRun tm2 1 outerLCIncZeroExitStart =
      some outerLCIncZeroExitEnd := by
  decide

theorem outerLCIncZeroExit_heads :
    (List.range 1).all (fun k =>
      match fRun tm2 k outerLCIncZeroExitStart with
      | none => true
      | some c => outerLCIncZeroExitInside c.head) = true := by
  decide

/-- Arbitrary-background lift of the one-step B-zero exit. -/
theorem outerLCIncZeroExit_at (T : Int → Bool) (h : Int)
    (hzero : T h = false) :
    run tm2 1 ⟨1,h,T⟩ =
      some (frameAt T h outerLCIncZeroExitInside
        outerLCIncZeroExitEnd) := by
  apply bridgeAt T h outerLCIncZeroExitInside
    outerLCIncZeroExitStart outerLCIncZeroExitEnd 1 rfl
    outerLCIncZeroExit_exact outerLCIncZeroExit_heads
  intro x hx
  have : x = 0 := by simpa [outerLCIncZeroExitInside] using hx
  subst x
  simpa [outerLCIncZeroExitStart] using hzero

#print axioms outerLCIncZeroExit_exact
#print axioms outerLCIncZeroExit_at

end BB6Coverage.Agent42OuterLCInc
