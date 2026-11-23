import CountedRst1Prime
import ChampionRootBridge
import Lean.Elab.Tactic.Omega

/-!
# Outer LC_Inc: fixed return-tail kernel

The general outer-counter postlude has a parameter-independent 28-step
return tail after its final right-unary zero exit.  At that point the
head is in state 2, the local input window (relative to the head) has
ones exactly at -3, 0, and 1, and the trace returns to state 3 four
cells to the left.  This file certifies that finite kernel and its
arbitrary-background frame lift.
-/

namespace BB6Coverage.Agent42OuterLCInc

open BB6Coverage
open BB6Coverage.Agent8Rst1Prime
open BB6Coverage.Agent48Champion

/-- The tail reads and writes only the finite interval [-3,5]. -/
def outerLCIncTailInside (x : Int) : Bool :=
  decide (-3 ≤ x ∧ x ≤ 5)

/-- State 2 at the rightmost one of the last 001 block, with the
following cell already written to one by the zero-exit transition. -/
def outerLCIncTailStart : FConfig :=
  ⟨2, 0, [-3, 0, 1]⟩

/-- Exact 28-step output.  Relative to the initial head, the final
state-3 head is -4 and the ones are at -2,-1,0,3,4,5. -/
def outerLCIncTailEnd : FConfig :=
  ⟨3, -4, [-2, -1, 0, 3, 4, 5]⟩

/-- The fixed 28-step return trace is an exact computation of tm2. -/
theorem outerLCIncTail_exact :
    fRun tm2 28 outerLCIncTailStart = some outerLCIncTailEnd := by
  decide

/-- Every pre-transition head position of the return trace lies in
[-3,5], so the finite computation lifts to arbitrary tapes. -/
theorem outerLCIncTail_heads :
    (List.range 28).all (fun k =>
      match fRun tm2 k outerLCIncTailStart with
      | none => true
      | some c => outerLCIncTailInside c.head) = true := by
  decide

/-- Original-source frame theorem for the fixed 28-step return tail.
Only the nine cells in the certified window are constrained; all
surrounding tape cells are preserved. -/
theorem outerLCIncTail_at (T : Int → Bool) (h : Int)
    (hmatch : ∀ x, outerLCIncTailInside x = true →
      T (h+x) = decide (x ∈ outerLCIncTailStart.marked)) :
    run tm2 28 ⟨2,h,T⟩ =
      some (frameAt T h outerLCIncTailInside outerLCIncTailEnd) := by
  exact bridgeAt T h outerLCIncTailInside
    outerLCIncTailStart outerLCIncTailEnd 28 rfl
    outerLCIncTail_exact outerLCIncTail_heads hmatch

#print axioms outerLCIncTail_exact
#print axioms outerLCIncTail_at

end BB6Coverage.Agent42OuterLCInc
