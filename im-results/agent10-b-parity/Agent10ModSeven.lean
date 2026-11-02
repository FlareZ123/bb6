import Agent10BParity

namespace BB6.Agent10B

/-- The odd 7 coefficient vanishes modulo seven under the shifted encoding. -/
theorem G_mod7_step (z : Nat) :
    (G z+8)%7 = (5*(z+8))%7 := by
  have h := two_T (z+8)
  rw [shifted_G] at h
  omega

/-- Exact parity-independent residue for arbitrary scalar initial state. -/
theorem G_mod7_iter (n z : Nat) :
    (iterG n z+8)%7 = (5^n*(z+8))%7 := by
  induction n generalizing z with
  | zero => simp [iterG]
  | succ n ih =>
    change (iterG n (G z)+8)%7 = (5^(n+1)*(z+8))%7
    rw [ih (G z)]
    have h := G_mod7_step z
    calc
      (5^n*(G z+8))%7 = ((5^n%7)*((G z+8)%7))%7 := by
        simp [Nat.mul_mod]
      _ = ((5^n%7)*((5*(z+8))%7))%7 := by rw [h]
      _ = (5^n*(5*(z+8)))%7 := by
        simpa only [Nat.mod_mod] using
          (Nat.mul_mod (5^n) (5*(z+8)) 7).symm
      _ = (5^(n+1)*(z+8))%7 := by
        have hmul : 5^n*(5*(z+8))=5^(n+1)*(z+8) := by
          rw [Nat.pow_succ]
          ac_rfl
        rw [hmul]

theorem G_blank_mod7 (n : Nat) :
    (iterG n 0+1)%7 = (5^n)%7 := by
  have h:=G_mod7_iter n 0
  simp only [Nat.zero_add] at h
  have ht : (iterG n 0+8)%7 = (iterG n 0+1)%7 := by omega
  have hr : (5^n*8)%7 = (5^n)%7 := by omega
  omega

theorem five_pow_mod7_six (q : Nat) :
    (5^(6*q))%7=1 := by
  rw [Nat.pow_mul, Nat.pow_mod]
  have h : (5^6)%7=1 := by decide
  rw [h]
  simp

theorem five_pow_mod7_reduced (n : Nat) :
    (5^n)%7=(5^(n%6))%7 := by
  have h : n=6*(n/6)+n%6 := by omega
  rw [h, Nat.pow_add, Nat.mul_mod]
  rw [five_pow_mod7_six (n/6)]
  simp

#print axioms G_mod7_step
#print axioms G_mod7_iter
#print axioms G_blank_mod7
#print axioms five_pow_mod7_reduced
end BB6.Agent10B
