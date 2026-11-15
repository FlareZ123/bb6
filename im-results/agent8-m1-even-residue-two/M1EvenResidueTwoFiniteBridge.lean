import ChampionRootBridge
import Lean.Elab.Tactic.Omega

/-!
# New finite bridge for the m=1, n=2 (mod 8) reset branch

The original TM63 table has a 40-step finite bridge from the post-left-sweep
window for `n=2` to state 4 at displacement +4.  The window must extend to
`[-11,4]): unlike the existing `n=6` bridge, the new run reads the two
additional left cells supplied by the third `d1` block in
`binDec 3 2 = d1 ++ d0 ++ d1`.

The finite trace and head confinement are checked by kernel reduction
(`decide`) against the original `tm2` transition table.  This file does
not yet prove the quantified S1 source-frame match, the E-scan/q4 suffix
composition, or the counted drain.
-/

namespace BB6Coverage.Agent8M1EvenResidueTwo

open BB6Coverage.Agent48Champion

/-- The finite bridge's exact source window. -/
def m1EvenResidueTwoInside (x : Int) : Bool :=
  decide (-11 ≤ x ∧ x ≤ 4)

/-- Post-left-sweep input for `m=1,n=2`, in coordinates relative to the
new state-3 head. -/
def m1EvenResidueTwoBridgeStart : FConfig :=
  ⟨3, 0, [-11,-10,-7,-6,-5,-4,-1,2,3,4]⟩

/-- Exact state-4 output after forty original TM63 transitions.  The list
order is intentional: `FConfig` equality compares lists, not sets. -/
def m1EvenResidueTwoBridgeEnd : FConfig :=
  ⟨4, 4, [3,2,1,-1,-4,-7,-8,-9,-11,-10,4]⟩

/-- Exact 40-step original-table computation. -/
theorem m1EvenResidueTwoBridge_exact :
    fRun tm2 40 m1EvenResidueTwoBridgeStart =
      some m1EvenResidueTwoBridgeEnd := by
  decide

/-- Every pre-transition head position in the 40-step trace stays inside
the finite window, so `bridgeAt` can lift this computation to arbitrary
source tapes matching the window. -/
theorem m1EvenResidueTwoBridge_heads :
    (List.range 40).all (fun k =>
      match fRun tm2 k m1EvenResidueTwoBridgeStart with
      | none => true
      | some f => m1EvenResidueTwoInside f.head) = true := by
  decide

#print axioms m1EvenResidueTwoBridge_exact
#print axioms m1EvenResidueTwoBridge_heads

end BB6Coverage.Agent8M1EvenResidueTwo
