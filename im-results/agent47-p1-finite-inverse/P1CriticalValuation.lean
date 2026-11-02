import P1NoRootOne

namespace BB6.Agent47P1

private theorem n_plus_two_lt_pow (n : Nat) (hn : 4 ≤ n) :
    n + 2 < 2^n := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hn
  subst n
  have hbound : ∀ k : Nat, k+6 < 16*2^k := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
        rw [Nat.pow_succ]
        omega
  have hh := hbound k
  simpa [Nat.pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hh

private theorem critical_shift_identity (n : Nat) (hn : 4 ≤ n) :
    (14*2^n-2*n-16)/2+6 = 7*2^n-(n+2) := by
  have hlt := n_plus_two_lt_pow n hn
  omega

/-- For exponents t<=n, divisibility of the shifted enormous output
    is exactly divisibility of the small index offset n+2. -/
theorem critical_shift_dvd_iff (n t : Nat) (hn : 4 ≤ n) (ht : t ≤ n) :
    (2^t ∣ 7*2^n-(n+2)) ↔ (2^t ∣ n+2) := by
  have hlt := n_plus_two_lt_pow n hn
  have hdiv : 2^t ∣ 7*2^n := by
    obtain ⟨q,hq⟩ := Nat.pow_dvd_pow 2 ht
    refine ⟨7*q, ?_⟩
    rw [hq]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  constructor
  · intro hd
    have hx : 2^t ∣ (7*2^n)-(7*2^n-(n+2)) := Nat.dvd_sub hdiv hd
    have hy : (7*2^n)-(7*2^n-(n+2))=n+2 := by omega
    rwa [hy] at hx
  · intro hd
    exact Nat.dvd_sub hdiv hd

theorem critical_shift_not_pow_n (n : Nat) (hn : 4 ≤ n) :
    ¬ (2^n ∣ 7*2^n-(n+2)) := by
  intro h
  have hplus : 2^n ∣ n+2 :=
    (critical_shift_dvd_iff n n hn (by omega)).mp h
  have hm : 2^n ≤ n+2 := Nat.le_of_dvd (by omega) hplus
  have hlt := n_plus_two_lt_pow n hn
  omega

/-- EXACT 2-adic valuation equivalence for all exponents, no cutoff. -/
theorem critical_shift_all_powers (n t : Nat) (hn : 4 ≤ n) :
    (2^t ∣ 7*2^n-(n+2)) ↔ (2^t ∣ n+2) := by
  by_cases ht : t ≤ n
  · exact critical_shift_dvd_iff n t hn ht
  have hnt : n ≤ t := by omega
  have hpow : 2^n ∣ 2^t := Nat.pow_dvd_pow 2 hnt
  have hnoS : ¬ (2^t ∣ 7*2^n-(n+2)) := by
    intro h
    exact critical_shift_not_pow_n n hn (Nat.dvd_trans hpow h)
  have hnoSmall : ¬ (2^t ∣ n+2) := by
    intro h
    have hsmall : 2^n ∣ n+2 := Nat.dvd_trans hpow h
    have hge := Nat.le_of_dvd (by omega : 0<n+2) hsmall
    have hlt := n_plus_two_lt_pow n hn
    omega
  simp [hnoS, hnoSmall]

/-- The identical 2-adic statement in actual GAncestor output coordinates. -/
theorem critical_hub_shift_all_powers (n t : Nat) (hn : 4 ≤ n) :
    (2^t ∣ 3+(14*2^n-2*n-16)/2+3) ↔ (2^t ∣ n+2) := by
  have hid := critical_shift_identity n hn
  have hsum : 3+(14*2^n-2*n-16)/2+3 = 7*2^n-(n+2) := by omega
  rw [hsum]
  exact critical_shift_all_powers n t hn

/-- Every positive G inverse of a critical hub has inverse depth at most
    floor(log2(n+2)), independent of the enormous 2^n tape counter. -/
theorem critical_hub_log_depth (n k c : Nat) (hn : 4 ≤ n)
    (h : BB6.P1Reduction.GAncestor (14*2^n-2*n-16) 3 k c) :
    ∃ t : Nat, t ≤ Nat.log2 (n+2) ∧
       3+(14*2^n-2*n-16)/2+3 = 2^t*(c+3) := by
  obtain ⟨t,ht⟩ := BB6.P1Reduction.GAncestor_power _ _ _ _ h
  have hdiv : 2^t ∣ 3+(14*2^n-2*n-16)/2+3 := ⟨c+3,ht⟩
  have hplus : 2^t ∣ n+2 := (critical_hub_shift_all_powers n t hn).mp hdiv
  have hle : 2^t ≤ n+2 := Nat.le_of_dvd (by omega) hplus
  exact ⟨t, (Nat.le_log2 (by omega : n+2 ≠ 0)).mpr hle, ht⟩

#print axioms critical_hub_log_depth

#print axioms critical_shift_dvd_iff
#print axioms critical_shift_all_powers
#print axioms critical_hub_shift_all_powers
#print axioms critical_shift_not_pow_n
end BB6.Agent47P1
