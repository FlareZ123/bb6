import Sheep138ChildExceptional
import SheepEvenSourceAlgebra

namespace Sheep138ChildGateway

/-- Every actual blank-root path to the first rational child has a generic
last even-section return with h≤3. -/
theorem child1_generic_predecessor (k y : Nat)
    (ht : 15*y+2=2^(141+4860*k))
    (hr : SheepEven.EvenReach 10 y) :
    ∃ x a h v u : Nat,
      SheepEven.EvenReach 10 x ∧ SheepEven.EvenEdge x y ∧
      1≤a ∧ h<4 ∧ 5≤v ∧ v%2=1 ∧ u%2=1 ∧
      x=2^a*v ∧ 2*(1+2^h*u)+1=(2^(a+1)+1)*v+2*a ∧
      y=1+3^h*u := by
  have hneq : 10 ≠ y := by
    intro he
    have hp : 2^141≤2^(141+4860*k) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hbase : 152<2^141 := by decide
    rw [←he] at ht
    omega
  obtain ⟨x,hreach,hedge⟩ := SheepEvenReachInverse.reach_last_edge hr hneq
  have hxeven : x%2=0 := SheepEvenReachInverse.even_reach_preserves_even hreach (by decide)
  rcases SheepEvenSourceAlgebra.even_edge_to_algebra hxeven hedge with
    ⟨a,h,v,u,ha,hv,hvodd,hu,hx,hz,hy⟩ |
    ⟨a,h,u,ha,hu,hx,hz,hy⟩
  · have hsmall := Sheep138ChildHighH.child1_h_lt_four k y h u ht hy
    exact ⟨x,a,h,v,u,hreach,hedge,ha,hsmall,hv,hvodd,hu,hx,hz,hy⟩
  · exact False.elim (Sheep138ChildExceptional.child1_no_special k y a h u ht hy hz)

/-- Every actual blank-root path to the second rational child has a generic
last even-section return with h≤1. -/
theorem child2_generic_predecessor (k y : Nat)
    (ht : 81*y+68=2^(143+4860*k))
    (hr : SheepEven.EvenReach 10 y) :
    ∃ x a h v u : Nat,
      SheepEven.EvenReach 10 x ∧ SheepEven.EvenEdge x y ∧
      1≤a ∧ h<2 ∧ 5≤v ∧ v%2=1 ∧ u%2=1 ∧
      x=2^a*v ∧ 2*(1+2^h*u)+1=(2^(a+1)+1)*v+2*a ∧
      y=1+3^h*u := by
  have hneq : 10 ≠ y := by
    intro he
    have hp : 2^143≤2^(143+4860*k) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hbase : 878<2^143 := by decide
    rw [←he] at ht
    omega
  obtain ⟨x,hreach,hedge⟩ := SheepEvenReachInverse.reach_last_edge hr hneq
  have hxeven : x%2=0 := SheepEvenReachInverse.even_reach_preserves_even hreach (by decide)
  rcases SheepEvenSourceAlgebra.even_edge_to_algebra hxeven hedge with
    ⟨a,h,v,u,ha,hv,hvodd,hu,hx,hz,hy⟩ |
    ⟨a,h,u,ha,hu,hx,hz,hy⟩
  · have hsmall := Sheep138ChildHighH.child2_h_lt_two k y h u ht hy
    exact ⟨x,a,h,v,u,hreach,hedge,ha,hsmall,hv,hvodd,hu,hx,hz,hy⟩
  · exact False.elim (Sheep138ChildExceptional.child2_no_special k y a h u ht hy hz)

#print axioms child1_generic_predecessor
#print axioms child2_generic_predecessor
end Sheep138ChildGateway
