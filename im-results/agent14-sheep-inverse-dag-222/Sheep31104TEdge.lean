import SheepEvenSourceAlgebra
import Sheep31104TComplete

namespace Sheep31104TEdge

/-- The genuine source-derived Sheep even-return graph has no incoming
edge to the terminal affine T node, for any k. -/
theorem no_original_edge_into_T (k x y : Nat)
    (hx : x%2=0)
    (hedge : SheepEven.EvenEdge x y)
    (hy : 31347*y+174404=2^(31117+122472*k)) : False := by
  have hcases :=
    SheepEvenSourceAlgebra.original_even_edge_inverse_cases hx hedge hy
  exact Sheep31104TComplete.T_no_source k x y hy hcases

#print axioms no_original_edge_into_T
end Sheep31104TEdge
