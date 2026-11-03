import Sheep138NoIncoming
import Sheep138RootCases
import Sheep138GenericHigh
import Sheep138HighH
import Sheep138Exceptional
import SheepEvenSourceAlgebra

namespace Sheep138RootShield

/-- Every even predecessor of the r138 power belongs to one of two
rational families, without assuming the predecessor is blank-reachable. -/
theorem any_root_parent_is_child (k x y : Nat)
    (heven : x % 2 = 0)
    (hedge : SheepEven.EvenEdge x y)
    (ht : y=2^(138+4860*k)) :
    (15*x+2=2^(141+4860*k)) ∨ (81*x+68=2^(143+4860*k)) := by
  rcases SheepEvenSourceAlgebra.even_edge_to_algebra heven hedge with
    ⟨a,h,v,u,ha,hv,hvodd,hu,hx,hz,hy⟩ |
    ⟨a,h,u,ha,hu,hx,hz,hy⟩
  · have htarget : 2^(138+4860*k)=1+3^h*u := by
      rw [←ht]
      exact hy
    have hlt : h < 3 :=
      Sheep138HighH.root_predecessor_h_lt_three k h u htarget
    have hcases : h=0 ∨ h=1 ∨ h=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst h
      by_cases hsmall : a<2
      · have heq : a=1 := by omega
        subst a
        exact False.elim (Sheep138RootCases.no_case_0_1 k v u hvodd htarget hz)
      · exact False.elim (Sheep138GenericHigh.high_h0
          (138+4860*k) a v u (by omega) (by simpa using htarget) (by simpa using hz))
    · subst h
      by_cases hsmall : a<5
      · have acases : a=1 ∨ a=2 ∨ a=3 ∨ a=4 := by omega
        rcases acases with ha1 | ha2 | ha3 | ha4
        · subst a
          have hp : 2^(141+4860*k)=8*2^(138+4860*k) := by
            rw [show 141+4860*k=(138+4860*k)+3 by omega,Nat.pow_add]
            omega
          have hchild : 15*x+2=2^(141+4860*k) := by
            rw [hx,hp]
            omega
          exact Or.inl hchild
        · subst a
          exact False.elim (Sheep138RootCases.no_case_1_2 k v u hvodd htarget hz)
        · subst a
          exact False.elim (Sheep138RootCases.no_case_1_3 k v u hvodd htarget hz)
        · subst a
          exact False.elim (Sheep138RootCases.no_case_1_4 k v u hvodd htarget hz)
      · exact False.elim (Sheep138GenericHigh.high_h1
          (138+4860*k) a v u (by omega) htarget hz)
    · subst h
      by_cases hsmall : a<7
      · have acases : a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 := by omega
        rcases acases with ha1 | ha2 | ha3 | ha4 | ha5 | ha6
        · subst a
          exact False.elim (Sheep138RootCases.no_case_2_1 k v u hvodd htarget hz)
        · subst a
          have hp : 2^(143+4860*k)=32*2^(138+4860*k) := by
            rw [show 143+4860*k=(138+4860*k)+5 by omega,Nat.pow_add]
            omega
          have hchild : 81*x+68=2^(143+4860*k) := by
            rw [hx,hp]
            omega
          exact Or.inr hchild
        · subst a
          exact False.elim (Sheep138RootCases.no_case_2_3 k v u hvodd htarget hz)
        · subst a
          exact False.elim (Sheep138RootCases.no_case_2_4 k v u hvodd htarget hz)
        · subst a
          exact False.elim (Sheep138RootCases.no_case_2_5 k v u hvodd htarget hz)
        · subst a
          exact False.elim (Sheep138RootCases.no_case_2_6 k v u hvodd htarget hz)
      · exact False.elim (Sheep138GenericHigh.high_h2
          (138+4860*k) a v u (by omega) htarget hz)
  · have htarget : 2^(138+4860*k)=1+3^h*u := by
      rw [←ht]
      exact hy
    exact False.elim (Sheep138Exceptional.no_special_predecessor
      k a h u hz htarget)

/-- The target of a genuine first-even Sheep return is even. -/
theorem even_edge_target_even {x y : Nat}
    (hx : x%2=0) (edge : SheepEven.EvenEdge x y) : y%2=0 := by
  rcases SheepEvenSourceAlgebra.even_edge_to_algebra hx edge with
    ⟨a,h,v,u,ha,hv,hvodd,hu,hxdef,hz,hy⟩ |
    ⟨a,h,u,ha,hu,hxdef,hz,hy⟩
  · rw [hy]
    have h3 : 3^h % 2 = 1 := by simp [Nat.pow_mod]
    simp [Nat.add_mod, Nat.mul_mod, h3, hu]
  · rw [hy]
    have h3 : 3^h % 2 = 1 := by simp [Nat.pow_mod]
    simp [Nat.add_mod, Nat.mul_mod, h3, hu]

/-- No chain of TWO consecutive even-section returns, from any even source,
can land in the r138 halting-power family. -/
theorem no_two_step_parent (k x z y : Nat)
    (hx : x%2=0)
    (e1 : SheepEven.EvenEdge x z)
    (e2 : SheepEven.EvenEdge z y)
    (ht : y=2^(138+4860*k)) : False := by
  have hz : z%2=0 := even_edge_target_even hx e1
  rcases any_root_parent_is_child k z y hz e2 ht with h1 | h2
  · exact Sheep138NoIncoming.child1_no_incoming k x z hx e1 h1
  · exact Sheep138NoIncoming.child2_no_incoming k x z hx e1 h2

#print axioms any_root_parent_is_child
#print axioms even_edge_target_even
#print axioms no_two_step_parent
end Sheep138RootShield
