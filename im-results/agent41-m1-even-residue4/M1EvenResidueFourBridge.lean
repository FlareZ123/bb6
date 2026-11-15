import ChampionRootBridge

/-!
Finite original-TM2 bridge for the candidate m=1, n=8*k+4 reset row.
This module is a proof candidate and has not yet been Lean-compiled.
-/

namespace BB6Coverage.Agent41M1EvenResidueFour

open BB6Coverage.Agent48Champion

/-- The finite bridge's exact read/head window. -/
def m1EvenResidueFourInside (x : Int) : Bool :=
  decide (-12 ≤ x ∧ x ≤ 5)

/-- Exact post-left-sweep finite input window, in coordinates relative to
the new state-3 head. -/
def m1EvenResidueFourBridgeStart : FConfig :=
  ⟨3, 0, [-10,-9,-8,-7,-6,-5,-4,-1,2,3,4,5]⟩

/-- Exact state-4 output window after 53 original TM2 transitions. -/
def m1EvenResidueFourBridgeEnd : FConfig :=
  ⟨4, 5, [-12,-11,-10,-7,-4,-1,1,2,3,4,5]⟩

/-- The 53-step bridge is a finite computation over the original table. -/
theorem m1EvenResidueFourBridge_exact :
    fRun tm2 53 m1EvenResidueFourBridgeStart =
      some m1EvenResidueFourBridgeEnd := by
  decide

/-- Every pre-final head position stays inside the bridge's exact window. -/
theorem m1EvenResidueFourBridge_heads :
    (List.range 53).all (fun k =>
      match fRun tm2 k m1EvenResidueFourBridgeStart with
      | none => true
      | some f => m1EvenResidueFourInside f.head) = true := by
  decide

theorem m1EvenResidueFourBridge_end_inside :
    m1EvenResidueFourInside m1EvenResidueFourBridgeEnd.head = true := by
  decide

#print axioms m1EvenResidueFourBridge_exact
#print axioms m1EvenResidueFourBridge_heads
#print axioms m1EvenResidueFourBridge_end_inside

end BB6Coverage.Agent41M1EvenResidueFour
