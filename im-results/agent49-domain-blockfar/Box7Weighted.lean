import Box7Cover
import SparseBlankDelay

namespace BB6.Agent49Box7
open BB6Coverage BB6.Agent13BlankDelay

theorem box7_weighted (B : Nat) (hB : 41 ≤ B) (m : Machine)
    (hm : BB6.Agent49BoxOneHalt.Fits baseBox m) : WeightedBound B m := by
  intro k d hk hd
  have h := box7_upper m hm k hk
  have hlt : d < 6 := List.mem_range.mp (List.mem_filter.mp hd).1
  omega

#print axioms box7_weighted
end BB6.Agent49Box7
