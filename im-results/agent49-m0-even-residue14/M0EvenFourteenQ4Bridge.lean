import ChampionRootBridge
import Lean.Elab.Tactic.Omega

/-!
# m=0, n=32*k+14 finite q4 bridge

This is the 39-step finite bridge obtained after the 3a-cell left sweep
for the next root family `S1(L,32*k+14,0,a,0,b,h)`.  Its local input
window is [-9,2], and the finite head trace stays entirely inside that
window.  The higher-order binary tail is not part of this finite
certificate; a separate frame/input-match theorem is still required.
-/

namespace BB6Coverage.Agent49M0EvenFourteenQ4Bridge

open BB6Coverage
open BB6Coverage.Agent48Champion

def m0EvenFourteenInside (x : Int) : Bool :=
  decide (-9 ≤ x ∧ x ≤ 2)

def m0EvenFourteenBridgeStart : FConfig :=
  ⟨3, 0, [-7,-6,-5,-4,-1,2]⟩

def m0EvenFourteenBridgeEnd : FConfig :=
  ⟨4, 3, [-9,-8,-7,-4,-1,1,2]⟩

/-- Exact 39-step run of the original TM2 table on the finite window. -/
theorem m0EvenFourteenBridge_exact :
    fRun tm2 39 m0EvenFourteenBridgeStart =
      some m0EvenFourteenBridgeEnd := by
  decide

/-- Every pre-transition head remains in the [-9,2] bridge window. -/
theorem m0EvenFourteenBridge_heads :
    (List.range 39).all (fun k =>
      match fRun tm2 k m0EvenFourteenBridgeStart with
      | none => true
      | some f => m0EvenFourteenInside f.head) = true := by
  decide

#print axioms m0EvenFourteenBridge_exact
#print axioms m0EvenFourteenBridge_heads

end BB6Coverage.Agent49M0EvenFourteenQ4Bridge