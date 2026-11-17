import CountedRst1Prime
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

end BB6Coverage.Agent42OuterLCInc
