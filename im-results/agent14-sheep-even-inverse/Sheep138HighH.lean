import SheepEvenReachInverse

namespace Sheep138HighH

/-- Correct original r=138 root power modulo 27 for every k. -/
theorem root_not_one_mod27 (k : Nat) :
    2^(138+4860*k) % 27 ≠ 1 := by
  have hp : 2^18%27=1 := by decide
  have he : 138+4860*k=12+18*(7+270*k) := by omega
  have hp2 : (2^18)^(7+270*k)%27=1 := by
    rw [Nat.pow_mod (2^18) (7+270*k) 27, hp]
    simp
  rw [he, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, hp2]
  decide

/-- All original E predecessors of the r=138 halting-power target have
h=0,1,2. This is a genuine complete all-k source restriction. -/
theorem root_predecessor_h_lt_three
    (k h u : Nat)
    (hForm : 2^(138+4860*k) = 1+3^h*u) : h<3 := by
  by_cases hsmall : h < 3
  · exact hsmall
  have hge : 3≤h := by omega
  obtain ⟨t, ht⟩ : ∃ t, h=3+t := ⟨h-3,by omega⟩
  have hpow3 : 3^h=27*3^t := by
    rw [ht,Nat.pow_add]
  rw [hpow3] at hForm
  have hmod : 2^(138+4860*k)%27=1 := by
    rw [hForm,Nat.add_mod]
    have hm : (27*3^t*u)%27=0 := by simp [Nat.mul_mod]
    rw [hm]
  exact False.elim (root_not_one_mod27 k hmod)

/-- An actual last edge into a reachable r=138 halting-power target has
valuation h below three, while preserving the full blank-prefix witness. -/
theorem blank_root_h_lt_three (k : Nat)
    (hreach : SheepEven.EvenReach 10 (2^(138+4860*k))) :
    ∃ x z h u : Nat,
      SheepEven.EvenReach 10 x ∧ SheepEven.Step x z ∧ 5 ≤ z ∧
      u%2=1 ∧ z=1+2^h*u ∧
      2^(138+4860*k)=1+3^h*u ∧ h<3 := by
  have hneq : 10 ≠ 2^(138+4860*k) := by
    have hmon : 2^138 ≤ 2^(138+4860*k) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hbase : 10 < 2^138 := by decide
    omega
  obtain ⟨x,hx,hedge⟩ :=
    SheepEvenReachInverse.reach_last_edge hreach hneq
  obtain ⟨z,h,u,hs,hz5,hu,hz,hy⟩ := hedge
  have hlt := root_predecessor_h_lt_three k h u hy
  exact ⟨x,z,h,u,hx,hs,hz5,hu,hz,hy,hlt⟩

#print axioms blank_root_h_lt_three
#print axioms root_predecessor_h_lt_three
end Sheep138HighH
