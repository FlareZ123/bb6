import Lean.Elab.Tactic.Omega

namespace BB6.Agent11

/-- At every positive inverse depth, the authentic second-family
    arithmetic stopping parameters have j divisible by four.
    Thus they are outside previously certified M8 j≡2 (mod 4)
    halting-parameter classes. -/
theorem second_index_divisible_four (m r j q : Nat)
    (hm : m%4=3) (hr : 1≤r)
    (hX : j+3*m+3=2^(2*r+1)*(4*q+1)) : j%4=0 := by
  have hd : 4 ∣ 2^(2*r+1) := by
    have h : 2^2 ∣ 2^(2*r+1) := Nat.pow_dvd_pow 2 (by omega)
    simpa using h
  have hprod : 4∣2^(2*r+1)*(4*q+1) := by
    rcases hd with ⟨z,hz⟩
    refine ⟨z*(4*q+1),?_⟩
    rw [hz]
    ac_rfl
  have hmod : (j+3*m+3)%4=0 := by
    rw [hX]
    exact Nat.mod_eq_zero_of_dvd hprod
  omega

#print axioms second_index_divisible_four
end BB6.Agent11
