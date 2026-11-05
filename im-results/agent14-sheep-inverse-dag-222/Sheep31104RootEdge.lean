import SheepEvenSourceAlgebra
import Sheep31104RootComplete

namespace Sheep31104RootEdge

/-- Source-level inverse completeness for an authentic Sheep first-even
return into the 31104+122472*k power root. Every even predecessor has
the exact Z affine identity, uniformly in k. -/
theorem original_edge_to_root_has_Z_source (k x : Nat)
    (hx : x%2=0)
    (hedge : SheepEven.EvenEdge x (2^(31104+122472*k))) :
    3483*x+16576=2^(31114+122472*k) := by
  have hpower : (1:Nat)*2^(31104+122472*k)+0 =
      2^(31104+122472*k) := by omega
  have hcases :=
    SheepEvenSourceAlgebra.original_even_edge_inverse_cases hx hedge hpower
  exact Sheep31104RootComplete.root_parent_is_Z k x hcases

#print axioms original_edge_to_root_has_Z_source
end Sheep31104RootEdge
