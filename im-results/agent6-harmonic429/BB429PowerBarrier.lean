import Lean.Elab.Tactic.Omega
namespace BB429PowerBarrier

/-- For any first-branch endpoint obeying the exact BB429 first-burst formula,
    a prefix at least k long forces (a+3) to vanish mod 2^k. The formula itself
    is certified for genuine firstRun in Agent5's BB429Burst.prefix_formula. -/
theorem long_first_burst_divisible (u a n k : Nat)
    (hk : k ≤ n)
    (h : a+3=(u+3)*2^n) : (a+3)%(2^k)=0 := by
  obtain ⟨q,hq⟩ := Nat.pow_dvd_pow 2 hk
  have hd : 2^k ∣ a+3 := by
    refine ⟨(u+3)*q, ?_⟩
    calc
      a+3 = (u+3)*2^n := h
      _ = (u+3)*((2^k)*q) := by rw [hq]
      _ = (2^k)*((u+3)*q) := by
        simp only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  exact Nat.mod_eq_zero_of_dvd hd

/-- In particular, every first-branch prefix of length ≥5, when it exists,
    terminates with first counter ≡29 mod 32. This is one of the six globally
    surviving necessary halting residues. -/
theorem any_long_burst_terminal_mod32 (u a n : Nat)
    (hn : 5 ≤ n)
    (h : a+3=(u+3)*2^n) : a%32=29 := by
  have hh : (a+3)%32=0 := long_first_burst_divisible u a n 5 hn h
  omega

#print axioms any_long_burst_terminal_mod32
#print axioms long_first_burst_divisible
end BB429PowerBarrier
