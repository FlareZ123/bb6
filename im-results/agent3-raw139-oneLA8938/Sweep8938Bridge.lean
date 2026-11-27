import Raw139Affine8938Never
import FastThreeHoleAudit
import WeightedFirstOneCover

namespace BB6.Agent48Raw139E0OneLASweeps.Sweep8938
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay

def ctr : PartialMachine := fromCodes [7,8,11,21,14,13,17,16,2,11,19,24]
theorem same : ctr = BB6Coverage.Agent3Affine8938.table :=
  BB6.Agent31ThreeHole.tableOK_sound _ _ (by decide +kernel)
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m := by
  apply BB6Coverage.Agent3Affine8938.never m
  rw [← same]
  exact hm
theorem all_completions_weighted (B : Nat) (m : Machine)
    (hm : compatible ctr m) : WeightedBound B m :=
  weighted_of_never B m (never m hm)
#print axioms same
#print axioms never
#print axioms all_completions_weighted
end BB6.Agent48Raw139E0OneLASweeps.Sweep8938
