import EvenEdge
import SheepAffineSpecial

namespace SheepAffineSpecial

/-- Any incoming even edge into a sufficiently large affine binary ray is
    generic. This imports the original certified Sheep first-even model. -/
theorem affine_even_edge_generic {x y D L R A N n : Nat}
    (hx : x%2=0) (edge : SheepEven.EvenEdge x y)
    (hD : 0<D) (hA : 4≤A)
    (hbase : (D+L+R)*((A+2)^3+(A+2)) < 2^A)
    (hsmall : D*(1+(3*2^A+A+2)^2)+L < 2^N)
    (hn : N≤n) (hy : D*y+L=2^n+R) :
    ∃ a v h u : Nat, 1≤a ∧ 5≤v ∧ v%2=1 ∧ u%2=1 ∧
      x=2^a*v ∧ 2*(1+2^h*u)+1=(2^(a+1)+1)*v+2*a ∧
      y=1+3^h*u := by
  obtain ⟨z,h,u,hs,hz5,hu,hz,hout⟩ := edge
  cases hs with
  | special a =>
    exfalso
    exact no_special_affine D L R A N a h u n hD hA hbase hsmall hn
      (by omega) (by rw [← hout]; exact hy)
  | generic a v hv hmin =>
    have ha : 1≤a := by
      cases a with
      | zero => simp at hx; omega
      | succ a => omega
    have hhalf : 2*((v-1)/2)+1=v := by omega
    have hformula :
        2*(1+2^h*u)+1 = (2^(a+1)+1)*v + 2*a := by
      rw [← hz, Nat.pow_succ]
      grind
    exact ⟨a,v,h,u,ha,hmin,hv,hu,rfl,hformula,hout⟩

theorem h4_X_generic {x y a : Nat}
    (hx : x%2=0) (edge : SheepEven.EvenEdge x y)
    (ha : 34≤a) (hy : 3*y+4=2^(a+3)) :
    ∃ b v h u : Nat, 1≤b ∧ 5≤v ∧ v%2=1 ∧ u%2=1 ∧
      x=2^b*v ∧ 2*(1+2^h*u)+1=(2^(b+1)+1)*v+2*b ∧
      y=1+3^h*u :=
  affine_even_edge_generic (D:=3) (L:=4) (A:=16) (N:=37) (R:=0) (n:=a+3) hx edge
    (by decide) (by decide) (by decide) (by decide) (by omega) (by simpa using hy)

theorem h4_x_generic {x y a : Nat}
    (hx : x%2=0) (edge : SheepEven.EvenEdge x y)
    (ha : 59≤a) (hy : 2187*y+1868=2^(a+10)) :
    ∃ b v h u : Nat, 1≤b ∧ 5≤v ∧ v%2=1 ∧ u%2=1 ∧
      x=2^b*v ∧ 2*(1+2^h*u)+1=(2^(b+1)+1)*v+2*b ∧
      y=1+3^h*u :=
  affine_even_edge_generic (D:=2187) (L:=1868) (A:=27) (N:=69) (R:=0) (n:=a+10) hx edge
    (by decide) (by decide) (by decide) (by decide) (by omega) (by simpa using hy)

#print axioms affine_even_edge_generic
#print axioms h4_X_generic
#print axioms h4_x_generic
end SheepAffineSpecial
