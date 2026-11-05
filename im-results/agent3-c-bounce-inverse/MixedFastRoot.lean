import MixedFourNormalize
import FastRootFuel
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Execute Agent 11's source-exact fixed-target root decision only after
    all four mathematically forced predecessor regions are fully stripped.
    The remaining fuel is the normalized weighted mass, never the
    original target's potentially astronomical weighted mass. -/
def mixedFastRootDecision (x y : Nat) : Bool :=
  let p := mixedFourNormalize x y
  BB6.Agent11Fast.backwardFastFuel ((p.1+2*p.2)/2) p

/-- Full exact Boolean decision for true blank-origin Machine C reachability
    at every fixed target, composed from independent source-verified proofs. -/
theorem mixedFastRootDecision_iff (x y : Nat) :
    mixedFastRootDecision x y=true ↔ CReach x y := by
  unfold mixedFastRootDecision
  have hh := BB6.Agent11Fast.backwardFastFuelHalfFull_iff
    (mixedFourNormalize x y).1 (mixedFourNormalize x y).2
  change _ ↔ CReach (mixedFourNormalize x y).1 (mixedFourNormalize x y).2 at hh
  exact hh.trans (mixedFourNormalize_reach_iff x y).symm

#print axioms mixedFastRootDecision_iff
end BB6.Agent3
