import EvenEdge
import SheepEvenInverseAlgebra

namespace SheepEvenSourceAlgebra

/-- Every original-source first-even return out of an even input is covered
by the two exact arithmetic source cases, including the special u=3 case. -/
theorem even_edge_to_algebra {x y : Nat}
    (hx : x % 2 = 0) (edge : SheepEven.EvenEdge x y) :
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

/-- Entire original-source E-predecessor Diophantine splitter, valid for
all rational-exponential targets with natural negative offset. -/
theorem original_even_edge_inverse_cases
    {x y d c n : Nat} (hx : x%2=0)
    (edge : SheepEven.EvenEdge x y)
    (hy : d*y+c=2^n) :
    (∃ a h v u : Nat,
      1 ≤ a ∧ 5 ≤ v ∧ v%2=1 ∧ u%2=1 ∧
      x=2^a*v ∧ y=1+3^h*u ∧
      (d*3^h)*(2^(a+1)+1)*v + 2*a*(d*3^h) + 2^(h+1)*d + 2^(h+1)*c =
        2^(n+h+1) + 3*(d*3^h)) ∨
    (∃ a h u : Nat,
      1 ≤ a ∧ u%2=1 ∧
      x=3*2^a ∧ y=1+3^h*u ∧
      (d*3^h)*(3*2^a+a+2) + 2^h*d + 2^h*c = 2^(n+h)) := by
  exact SheepEvenInverseAlgebra.edge_inverse_negative_cases
    x y d c n (even_edge_to_algebra hx edge) hy

#print axioms even_edge_to_algebra
#print axioms original_even_edge_inverse_cases

end SheepEvenSourceAlgebra
