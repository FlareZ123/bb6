import ChampionRootBridge
import Lean.Elab.Tactic.Omega

/-!
# Finite bridge certificate for the M0-even n=8q+4 candidate

This file certifies only the finite 51-step TM2 trace and its head confinement.
It does not establish the arbitrary-source input frame, the E-scan, the q4
right-shape/left-facing identities, or the counted reset theorem.
-/ 

namespace BB6Coverage.Agent42M0EvenResidueFourBridge

open BB6Coverage
open BB6Coverage.Agent48Champion

def m0EvenFourBridgeInside (x : Int) : Bool :=
  decide (-12 ≤ x ∧ x ≤ 3)

def m0EvenFourBridgeStart : FConfig :=
  ⟨3, 0, [-10,-9,-8,-7,-6,-5,-4,-1,2,3]⟩

def m0EvenFourBridgeEnd : FConfig :=
  ⟨4, 3, [-12,-11,-10,-7,-4,-1,1,2,3]⟩

/-- Exact finite-list output of the 51 raw TM2 steps. -/
theorem m0EvenFourBridge_exact :
    fRun tm2 51 m0EvenFourBridgeStart =
      some m0EvenFourBridgeEnd := by
  decide

/-- Every pre-step head stays in the proposed local frame [-12,3]. -/
theorem m0EvenFourBridge_heads :
    (List.range 51).all (fun k =>
      match fRun tm2 k m0EvenFourBridgeStart with
      | none => true
      | some f => m0EvenFourBridgeInside f.head) = true := by
  decide

#print axioms m0EvenFourBridge_exact
#print axioms m0EvenFourBridge_heads

end BB6Coverage.Agent42M0EvenResidueFourBridge
