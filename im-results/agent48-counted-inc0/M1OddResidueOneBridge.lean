import ChampionRootBridge

/-!
# Finite bridge for the m=1, n=1 (mod 8) q4 prefix

After the counted left sweep of length 9*a+3, the n=8*k+1 source
family has the finite bridge input below.  The 29-step original-TM2
bridge ends at state 4/head 5, with all pre-final heads in [-9,4].
-/

namespace BB6Coverage.Agent48M1OddResidueOneBridge

open BB6Coverage.Agent48Champion

def m1OddResidueOneInside (x : Int) : Bool :=
  decide (-9 ≤ x ∧ x ≤ 4)

def m1OddResidueOneBridgeStart : FConfig :=
  ⟨3, 0, [-9,-8,-7,-4,-1,2,3,4]⟩

def m1OddResidueOneBridgeEnd : FConfig :=
  -- `FConfig.marked` is an ordered list; fMove prepends each newly written cell.
  ⟨4, 5, [4,3,2,1,-1,-4,-5,-6,-9,-8,-7]⟩

/-- Exact 29-step bridge for the m=1, n=1 (mod 8) source row. -/
theorem m1OddResidueOneBridge_exact :
    fRun tm2 29 m1OddResidueOneBridgeStart =
      some m1OddResidueOneBridgeEnd := by
  decide

/-- Every pre-final head remains inside the finite bridge window. -/
theorem m1OddResidueOneBridge_heads :
    (List.range 29).all (fun k =>
      match fRun tm2 k m1OddResidueOneBridgeStart with
      | none => true
      | some f => m1OddResidueOneInside f.head) = true := by
  decide

#print axioms m1OddResidueOneBridge_exact
#print axioms m1OddResidueOneBridge_heads

end BB6Coverage.Agent48M1OddResidueOneBridge
