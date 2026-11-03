import EvenReach
import SheepEvenSourceAlgebra

namespace SheepEvenReachInverse

/-- Reachability from an even origin stays within even first-return states. -/
theorem even_reach_preserves_even {x y : Nat}
    (h : SheepEven.EvenReach x y) (hx : x%2=0) : y%2=0 := by
  induction h with
  | refl x => exact hx
  | @cons x y z edge tail ih =>
    exact ih (SheepEven.even_edge_even edge)

/-- Any nonempty finite E-reach path has an actual last edge. -/
theorem reach_last_edge {x y : Nat}
    (h : SheepEven.EvenReach x y) (hne : x ≠ y) :
    ∃ z, SheepEven.EvenReach x z ∧ SheepEven.EvenEdge z y := by
  have split {a b : Nat} (h : SheepEven.EvenReach a b) :
      a=b ∨ ∃ z, SheepEven.EvenReach a z ∧ SheepEven.EvenEdge z b := by
    induction h with
    | refl a => exact Or.inl rfl
    | @cons a middle b first tail ih =>
      rcases ih with heq | ⟨z,hreach,hlast⟩
      · subst b
        exact Or.inr ⟨a,SheepEven.EvenReach.refl a,first⟩
      · exact Or.inr ⟨z,SheepEven.EvenReach.cons first hreach,hlast⟩
  rcases split h with heq | hlast
  · exact False.elim (hne heq)
  · exact hlast

/-- Every genuine nontrivial blank-even-root ancestor of a rational-power
 target must satisfy one of the complete source-checked inverse Diophantine
 equations; this is an all-time, no-horizon statement. -/
theorem blank_even_inverse_cases
    {y d c n : Nat} (hy : SheepEven.EvenReach 10 y)
    (hnot : y ≠ 10) (hpower : d*y+c=2^n) :
    (∃ x a h v u : Nat,
      SheepEven.EvenReach 10 x ∧
      1 ≤ a ∧ 5 ≤ v ∧ v%2=1 ∧ u%2=1 ∧
      x=2^a*v ∧ y=1+3^h*u ∧
      (d*3^h)*(2^(a+1)+1)*v + 2*a*(d*3^h) + 2^(h+1)*d + 2^(h+1)*c =
        2^(n+h+1)+3*(d*3^h)) ∨
    (∃ x a h u : Nat,
      SheepEven.EvenReach 10 x ∧
      1 ≤ a ∧ u%2=1 ∧
      x=3*2^a ∧ y=1+3^h*u ∧
      (d*3^h)*(3*2^a+a+2)+2^h*d+2^h*c=2^(n+h)) := by
  obtain ⟨x,hreach,hedge⟩ := reach_last_edge hy (by omega)
  have hx : x%2=0 := even_reach_preserves_even hreach (by decide)
  rcases SheepEvenSourceAlgebra.original_even_edge_inverse_cases hx hedge hpower with
    ⟨a,h,v,u,ha,hv,hvodd,huodd,hxdef,hydef,hEq⟩ |
    ⟨a,h,u,ha,huodd,hxdef,hydef,hEq⟩
  · exact Or.inl ⟨x,a,h,v,u,hreach,ha,hv,hvodd,huodd,hxdef,hydef,hEq⟩
  · exact Or.inr ⟨x,a,h,u,hreach,ha,huodd,hxdef,hydef,hEq⟩

#print axioms blank_even_inverse_cases

end SheepEvenReachInverse
