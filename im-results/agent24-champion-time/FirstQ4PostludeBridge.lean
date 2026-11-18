import CountedSweep
import CountedRst1Prime
import Lean.Elab.Tactic.Omega

/-!
# Fixed finite bridge at the end of the first positive-z q4 postlude

After the counted left sweep of the 3z one-cells, the head is at 5 and
the seven-cell window [-5,1] is exactly the input below. This file isolates
the remaining ten primitive TM2 transitions and their arbitrary-tape frame
lifting. The sweep-to-window match and full checkpoint equality are separate
source obligations.
-/

namespace BB6Coverage.Agent24FirstQ4Postlude

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8Rst1Prime

/-- The complete seven-cell region queried by the fixed postlude bridge. -/
def firstQ4PostludeInside : Int → Bool :=
  inWindow (-5) 1

/-- Relative finite input at head 5: bits 0010110 on offsets -5..1. -/
def firstQ4PostludeStart : FConfig :=
  ⟨3, 0, [-3, -1, 0]⟩

/-- Relative finite output at head 1: bits 1000011 on offsets -5..1. -/
def firstQ4PostludeEnd : FConfig :=
  ⟨4, -4, [-5, 0, 1]⟩

/-- Exact ten-step trace for the fixed postlude bridge. -/
theorem firstQ4Postlude_exact :
    fRun tm2 10 firstQ4PostludeStart =
      some firstQ4PostludeEnd := by
  decide

/-- Every head position queried by the finite bridge lies in [-5,1]. -/
theorem firstQ4Postlude_heads :
    (List.range 10).all (fun k =>
      match fRun tm2 k firstQ4PostludeStart with
      | none => true
      | some f => firstQ4PostludeInside f.head) = true := by
  decide

/-- Lift the fixed ten-step bridge to any infinite tape agreeing with the
finite input on [-5,1]. The surrounding tape is preserved outside the frame. -/
theorem firstQ4Postlude_at
    (T : Int → Bool) (h : Int)
    (hmatch : ∀ x, firstQ4PostludeInside x = true →
      T (h+x) = decide (x ∈ firstQ4PostludeStart.marked)) :
    run tm2 10 ⟨3,h,T⟩ =
      some (frameAt T h firstQ4PostludeInside firstQ4PostludeEnd) := by
  exact bridgeAt T h firstQ4PostludeInside
    firstQ4PostludeStart firstQ4PostludeEnd 10 rfl
    firstQ4Postlude_exact firstQ4Postlude_heads hmatch

#print axioms firstQ4Postlude_exact
#print axioms firstQ4Postlude_heads
#print axioms firstQ4Postlude_at

end BB6Coverage.Agent24FirstQ4Postlude
