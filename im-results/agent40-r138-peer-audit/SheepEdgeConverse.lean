import SheepGenericConverse

namespace SheepEdgeConverse

/-- The previously uncoupled exceptional odd-part-three algebraic branch
also suffices to construct a genuine source-level first-even return. -/
theorem special_to_source {x y : Nat}
    (hs : SheepEvenInverseAlgebra.SpecialEdge x y) :
    SheepEven.EvenEdge x y := by
  obtain ⟨a,h,u,ha,hu,hx,hz,hy⟩ := hs
  have hstep : SheepEven.Step x (1+2^h*u) := by
    rw [hx, ←hz]
    exact SheepEven.Step.special a
  have hz5 : 5 ≤ 1+2^h*u := by
    have hp : 0 < 2^a := Nat.pow_pos (by decide)
    omega
  exact ⟨1+2^h*u,h,u,hstep,hz5,hu,rfl,hy⟩

/-- Constructive converse to the exact two-branch inverse algebra,
including the exceptional odd-part-three Sheep constructor. -/
theorem algebra_edge_to_source {x y : Nat}
    (he : SheepEvenInverseAlgebra.Edge x y) :
    SheepEven.EvenEdge x y := by
  rcases he with hg | hs
  · exact SheepGenericConverse.generic_to_source hg
  · exact special_to_source hs

#print axioms special_to_source
#print axioms algebra_edge_to_source
end SheepEdgeConverse
