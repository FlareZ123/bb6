import GInverse
namespace BB6.P1Reduction

theorem pow_two_at_least_succ (n:Nat):n+1≤2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    omega

/-- Every G predecessor of an n-indexed critical c=3 gateway is governed
    by an exact power-of-two divisor of 7*2^n-n-2. -/
theorem critical_gateway_G_divisor (n k c:Nat) (hn:2≤n)
    (h:G k c=(14*2^n-2*n-16,3)) :
    ∃t:Nat, 7*2^n = 2^t*(c+3)+n+2 := by
  have hp:=pow_two_at_least_succ n
  have hb : 0<14*2^n-2*n-16 := by omega
  obtain ⟨t,ht⟩ := G_input_power k c (14*2^n-2*n-16) 3 h hb
  refine ⟨t,?_⟩
  omega

#print axioms BB6.P1Reduction.critical_gateway_G_divisor
end BB6.P1Reduction
