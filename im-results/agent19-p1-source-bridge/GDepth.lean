import GInverse
import HaltingFunnel

namespace BB6.Agent19.Depth

/-- Exact identity of Agent 1's generic inverse model and Agent 4's
    machine-certified P1 drain, on every pair of natural counters. -/
theorem G_agree (k c : Nat) :
    BB6.P1Reduction.G k c = BB6.HaltingFunnel.G k c := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
    by_cases hlow : c < 2*k
    · rw [BB6.P1Reduction.G, BB6.HaltingFunnel.G]
      simp only [hlow,dite_true]
      exact ih _ (by omega) _
    · by_cases hmid:c ≤ 2*k+1
      · rw [BB6.P1Reduction.G, BB6.HaltingFunnel.G]
        simp [hlow,hmid]
      · rw [BB6.P1Reduction.G, BB6.HaltingFunnel.G]
        simp [hlow,hmid]

theorem pow_bound : ∀ n:Nat, n+1≤2^n := by
  intro n
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

theorem high_power_mod8 (n:Nat) (hn:3≤n) : (2^n)%8=0 := by
  have he : n=n-3+3 := by omega
  rw [he,Nat.pow_add]
  simp

/-- For n >= 10 congruent 2 mod 8, an inverse G path into the exact
    critical odd-sector (H(n)-6,3) can recurse at most twice.
    Quantifies over every possible input pair, without finite search. -/
theorem G_critical_inverse_depth_two
    (n k c : Nat) (hn:10≤n) (hmod:n%8=2)
    (h:BB6.HaltingFunnel.G k c = (14*2^n-2*n-16,3)) :
    ∃ t:Nat, t≤2 ∧
      7*2^n-n-2 = 2^t*(c+3) := by
  let b:=14*2^n-2*n-16
  have hb0 := pow_bound n
  have hbn : 0<b := by dsimp [b]; omega
  have hred : BB6.P1Reduction.G k c = (b,3) := by
    rw [G_agree k c]
    exact h
  obtain ⟨t,ht⟩ := BB6.P1Reduction.G_input_power k c b 3 hred hbn
  have hformula : 3+b/2+3=7*2^n-n-2 := by dsimp [b]; omega
  rw [hformula] at ht
  refine ⟨t,?_,ht⟩
  by_cases ht2 : t≤2
  · exact ht2
  · exfalso
    have hlarge:3≤t := by omega
    have hp : (2^t)%8=0 := by
      have he : t=t-3+3 := by omega
      rw [he,Nat.pow_add]
      simp
    have hzero : (2^t*(c+3))%8=0 := by
      rw [Nat.mul_mod,hp]
      simp
    have hh : (7*2^n-n-2)%8=4 := by
      have he := high_power_mod8 n (by omega)
      omega
    omega

/-- Exhaustive classification of all possible right input counters in
    the recursive inverse of the residual critical odd-sector for
    n congruent 2 mod 8: exactly three arithmetic candidates. -/
theorem G_critical_inverse_c_three
    (n k c : Nat) (hn:10≤n) (hmod:n%8=2)
    (h:BB6.HaltingFunnel.G k c = (14*2^n-2*n-16,3)) :
    c = (7*2^n-n-2)-3 ∨
    c = (7*2^n-n-2)/2-3 ∨
    c = (7*2^n-n-2)/4-3 := by
  obtain ⟨t,htbound,ht⟩ := G_critical_inverse_depth_two n k c hn hmod h
  have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
  rcases hcases with heq | heq | heq
  · subst t
    simp at ht
    left
    omega
  · subst t
    simp at ht
    right; left
    omega
  · subst t
    simp at ht
    right; right
    omega

#print axioms BB6.Agent19.Depth.G_agree
#print axioms BB6.Agent19.Depth.G_critical_inverse_depth_two
#print axioms BB6.Agent19.Depth.G_critical_inverse_c_three

end BB6.Agent19.Depth
