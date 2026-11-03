import SheepEdgeConverse
namespace SheepExactEdgeEquiv

theorem source_to_algebra {x y : Nat}
    (hx : x%2=0) (edge : SheepEven.EvenEdge x y) :
    SheepEvenInverseAlgebra.Edge x y := by
  obtain ⟨z,h,u,hs,hz5,hu,hz,hy⟩ := edge
  cases hs with
  | special a =>
    have ha : 1 ≤ a := by
      cases a with
      | zero => simp at hx
      | succ a => omega
    exact Or.inr ⟨a,h,u,ha,hu,rfl,hz,hy⟩
  | generic a v hv hmin =>
    have ha : 1 ≤ a := by
      cases a with
      | zero => simp at hx; omega
      | succ a => omega
    have hhalf : 2*((v-1)/2)+1=v := by omega
    have hformula :
        2*(1+2^h*u)+1 = (2^(a+1)+1)*v + 2*a := by
      rw [← hz, Nat.pow_succ]
      grind
    exact Or.inl ⟨a,h,v,u,ha,hmin,hv,hu,rfl,hformula,hy⟩

theorem iff_original_source_on_even (x y : Nat) (hx : x%2=0) :
    SheepEven.EvenEdge x y ↔ SheepEvenInverseAlgebra.Edge x y := by
  constructor
  · exact source_to_algebra hx
  · exact SheepEdgeConverse.algebra_edge_to_source

#print axioms source_to_algebra
#print axioms iff_original_source_on_even
end SheepExactEdgeEquiv
