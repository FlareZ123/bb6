import Lean.Elab.Tactic.Omega

namespace BB6.Agent11

/-- Arithmetic disjointness: the two new M32 first-family stopping
    congruence classes cannot be certified by ANY of the previous
    even-depth M8 Diophantine barriers. No reachability axioms needed. -/
theorem m32_first_classes_not_m8 (m : Nat)
    (hm : m%2048=584 ∨ m%2048=1864) :
    ¬ ∃ r s t : Nat, m=64*s+8 ∧ 63*s+11=2^(2*r)*(4*t+1) := by
  intro h
  obtain ⟨r,s,t,hms,heq⟩ := h
  have hm256 : m%256=72 := by rcases hm with hm|hm <;> omega
  have hs4 : s%4=1 := by omega
  have hx4 : (63*s+11)%4=2 := by omega
  cases r with
  | zero =>
      have hr : (2^(2*0)*(4*t+1))%4=1 := by omega
      rw [heq] at hx4
      omega
  | succ r =>
      have h4 : 4 ∣ 2^(2*(r+1)) := by
        have hh : 2^2 ∣ 2^(2*(r+1)) := Nat.pow_dvd_pow 2 (by omega)
        simpa using hh
      have hp : 4 ∣ 2^(2*(r+1))*(4*t+1) := by
        obtain ⟨u,hu⟩ := h4
        refine ⟨u*(4*t+1),?_⟩
        rw [hu]
        ac_rfl
      have hr : (2^(2*(r+1))*(4*t+1))%4=0 := Nat.mod_eq_zero_of_dvd hp
      rw [heq] at hx4
      omega

#print axioms m32_first_classes_not_m8
end BB6.Agent11
