import ChampionRootBridge
import Lean.Elab.Tactic.Omega

/-!
A finite source-table bridge for the next (m,n)=(1,3) odd reset stage.
The 26-step certificate includes the final state-5 zero-cell write that
enters state 4 at head +2; the subsequent counted E-scan is separate.
-/

namespace BB6Coverage.Agent42M1OddQ4Bridge

open BB6Coverage.Agent48Champion

def m1OddQ4BridgeStart : FConfig :=
  ⟨3,0,[-4,-1]⟩

def m1OddQ4BridgeEnd : FConfig :=
  ⟨4,2,[1,-1,-4,-5,-6]⟩

def m1OddQ4BridgeInside (x : Int) : Bool :=
  decide (-6 ≤ x ∧ x ≤ 1)

/-- Exact finite-list output of the 26 raw TM63 steps. -/
theorem m1OddQ4Bridge_exact :
    fRun tm2 26 m1OddQ4BridgeStart = some m1OddQ4BridgeEnd := by
  decide

/-- Every pre-step head of the 26-step bridge stays in the local frame. -/
theorem m1OddQ4Bridge_heads :
    (List.range 26).all (fun k =>
      match fRun tm2 k m1OddQ4BridgeStart with
      | some c => m1OddQ4BridgeInside c.head
      | none => false) = true := by
  decide

#print axioms m1OddQ4Bridge_exact
#print axioms m1OddQ4Bridge_heads

end BB6Coverage.Agent42M1OddQ4Bridge
