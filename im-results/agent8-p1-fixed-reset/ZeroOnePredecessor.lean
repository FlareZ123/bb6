import Std

namespace BB6.Agent8Zero

private theorem two_pow_succ_ge (t : Nat) : t+1≤2^t := by
  induction t with
  | zero => decide
  | succ t ih =>
      rw [Nat.pow_succ]
      omega

/-- No valid odd-cone predecessor can produce the odd hub (12,19).
    Exact all-natural source inverse power/mass equations are hypotheses. -/
theorem no_odd_parent_of_12_19 (b d t : Nat)
    (hb : 8≤b) (hb4 : b%4=0)
    (hp : d+b/2+3=18*2^t)
    (hm : b+d=33+2*t) : False := by
  have hdiv : b/2≤b := Nat.div_le_self b 2
  have hUpper : 18*2^t≤36+2*t := by omega
  have hpow := two_pow_succ_ge t
  have ht : t≤1 := by omega
  have hbeven : b=2*(b/2) := by omega
  have h01 : t=0 ∨ t=1 := by omega
  rcases h01 with h0 | h1
  · simp [h0] at hp hm
    omega
  · simp [h1] at hp hm
    omega

/-- Every valid odd-cone predecessor of (12,15) is exactly (12,19),
    with inverse depth 1. -/
theorem only_odd_parent_of_12_15 (b d t : Nat)
    (hb : 8≤b) (hb4 : b%4=0)
    (hp : d+b/2+3=14*2^t)
    (hm : b+d=29+2*t) :
    b=12 ∧ d=19 ∧ t=1 := by
  have hdiv : b/2≤b := Nat.div_le_self b 2
  have hUpper : 14*2^t≤32+2*t := by omega
  have hpow := two_pow_succ_ge t
  have ht : t≤1 := by omega
  have hbeven : b=2*(b/2) := by omega
  have h01 : t=0 ∨ t=1 := by omega
  rcases h01 with h0 | h1
  · simp [h0] at hp hm
    omega
  · simp [h1] at hp hm
    omega

#print axioms BB6.Agent8Zero.no_odd_parent_of_12_19
#print axioms BB6.Agent8Zero.only_odd_parent_of_12_15
end BB6.Agent8Zero
