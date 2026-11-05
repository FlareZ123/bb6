namespace BB6.Agent43Numeric148

private def poly (u : Nat) : Nat := 2*u*u+15*u+22

private theorem linear_below_pow (u : Nat) (hu : 9 ≤ u) :
    4*u+17 ≤ 2^u := by
  have h : ∀ k : Nat, 4*(k+9)+17 ≤ 2^(k+9) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      have heq : (k+1)+9=(k+9)+1 := by omega
      rw [heq, Nat.pow_succ]
      omega
  have heq : (u-9)+9=u := by omega
  simpa only [heq] using h (u-9)

private theorem poly_increment (u : Nat) :
    poly (u+1)=poly u+(4*u+17) := by
  simp only [poly, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
  omega

private theorem poly_below_pow (u : Nat) (hu : 9 ≤ u) :
    poly u < 2^u := by
  have h : ∀ k : Nat, poly (k+9) < 2^(k+9) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      have hlin : 4*(k+9)+17 ≤ 2^(k+9) :=
        linear_below_pow (k+9) (by omega)
      have hinc := poly_increment (k+9)
      have hidx : (k+1)+9=(k+9)+1 := by omega
      rw [hidx, hinc, Nat.pow_succ]
      omega
  have heq : (u-9)+9=u := by omega
  simpa only [heq] using h (u-9)

private theorem shell_ge_9 (n : Nat) (hn : 512 ≤ n) :
    ∃ u : Nat, 9 ≤ u ∧ 2^u ≤ n ∧ n < 2^(u+1) := by
  have h : ∀ n : Nat, 512 ≤ n →
      ∃ u : Nat, 9 ≤ u ∧ 2^u ≤ n ∧ n < 2^(u+1) := by
    intro k
    induction k with
    | zero =>
      intro hk
      omega
    | succ k ih =>
      intro hk
      by_cases hk' : 512 ≤ k
      · obtain ⟨u,hu,hlo,hhi⟩ := ih hk'
        by_cases ht : k+1 < 2^(u+1)
        · exact ⟨u,hu,by omega,by simpa only [Nat.succ_eq_add_one] using ht⟩
        · have heq : k+1=2^(u+1) := by omega
          refine ⟨u+1,by omega,?_,?_⟩
          · simpa only [Nat.succ_eq_add_one,heq] using
              (Nat.le_refl (2^(u+1)))
          · have hlt : 2^(u+1)<2^((u+1)+1) :=
              Nat.pow_lt_pow_right (by decide) (by omega)
            simpa only [Nat.succ_eq_add_one,heq] using hlt
      · have heq : k+1=512 := by omega
        refine ⟨9,by decide,?_,?_⟩
        · simpa only [Nat.succ_eq_add_one,heq] using
            (show (2:Nat)^9 ≤ 512 by decide)
        · simpa only [Nat.succ_eq_add_one,heq] using
            (show 512 < (2:Nat)^(9+1) by decide)
  exact h n hn

#print axioms BB6.Agent43Numeric148.linear_below_pow
#print axioms BB6.Agent43Numeric148.poly_increment
#print axioms BB6.Agent43Numeric148.poly_below_pow
#print axioms BB6.Agent43Numeric148.shell_ge_9

end BB6.Agent43Numeric148
