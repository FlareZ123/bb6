import SheepEvenSourceAlgebra
import Sheep31104ZComplete

namespace Sheep31104ZEdge

/-- An authentic even Sheep E edge into the affine node Z must originate in
the affine node T, uniformly for every parameter k. Inference uses the
full original-source generic/special inverse case splitter. -/
theorem original_edge_to_Z_has_T_source (k x y : Nat)
    (hx : x%2=0)
    (hedge : SheepEven.EvenEdge x y)
    (hy : 3483*y+16576=2^(31114+122472*k)) :
    31347*x+174404=2^(31117+122472*k) := by
  have hcases :=
    SheepEvenSourceAlgebra.original_even_edge_inverse_cases hx hedge hy
  exact Sheep31104ZComplete.Z_parent_is_T k x y hy hcases

#print axioms original_edge_to_Z_has_T_source

end Sheep31104ZEdge
