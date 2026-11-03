import Sheep138Exceptional

namespace Sheep138Gateway

/-- A genuine blank-entered r=138 halting power would have a preceding
blank-reachable *generic* first-even return with h<3. The special
odd-part-three return is globally impossible at these targets. -/
theorem blank_root_generic_predecessor (k : Nat)
    (hr : SheepEven.EvenReach 10 (2^(138+4860*k))) :
    ∃ x a h v u : Nat,
      SheepEven.EvenReach 10 x ∧
      SheepEven.EvenEdge x (2^(138+4860*k)) ∧
      1 ≤ a ∧ h < 3 ∧ 5 ≤ v ∧ v%2=1 ∧ u%2=1 ∧
      x=2^a*v ∧
      2*(1+2^h*u)+1 = (2^(a+1)+1)*v+2*a ∧
      2^(138+4860*k)=1+3^h*u := by
  have hneq : 10 ≠ 2^(138+4860*k) := by
    have hmon : 2^138 ≤ 2^(138+4860*k) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hbase : 10<2^138 := by decide
    omega
  obtain ⟨x,hx,hedge⟩ := SheepEvenReachInverse.reach_last_edge hr hneq
  have hxEven : x%2=0 := SheepEvenReachInverse.even_reach_preserves_even hx (by decide)
  rcases SheepEvenSourceAlgebra.even_edge_to_algebra hxEven hedge with
    ⟨a,h,v,u,ha,hv,hvodd,hu,hxdef,hformula,houtput⟩ |
    ⟨a,h,u,ha,hu,hxdef,hformula,houtput⟩
  · have hlt := Sheep138HighH.root_predecessor_h_lt_three k h u houtput
    exact ⟨x,a,h,v,u,hx,hedge,ha,hlt,hv,hvodd,hu,hxdef,hformula,houtput⟩
  · exact False.elim
      (Sheep138Exceptional.no_special_predecessor k a h u hformula houtput)

#print axioms blank_root_generic_predecessor
end Sheep138Gateway
