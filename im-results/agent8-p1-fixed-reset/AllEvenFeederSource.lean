import ZeroEvenBudgetSource
import UnifiedFeederSource

namespace BB6.Agent8Reset
open BB6.Agent28 BB6.Agent1Quarter BB6.Agent47P1

/-- In the authentic critical odd inverse cone, a polynomial reset
budget strictly below the affine-wall threshold excludes all even
inverse outputs (including c=0) whose successor is genuinely blank
reachable, and the exceptional odd successor c=1 (d=5).
The statement makes no claim about other odd continuations. -/
theorem source_no_low_budget_all_even_feeders
    (n b d m z : Nat) (hn : 14≤n)
    (hcone : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hSmall : budget (n+2) z*(3*budget (n+2) z+3*n+8)<7*2^n)
    (hgate : d=5 ∨
      ∃ t k c : Nat,
        8≤b ∧ b%4=0 ∧ inverseAt b d t=some(k,c) ∧
        2≤k ∧ c%2=0 ∧ BB6.Agent1.Reach (2*k-4) (c+4)) :
    False := by
  let T := budget (n+2) z
  have hfactor : 7≤3*T+3*n+8 := by omega
  have htimes : 7*T≤T*(3*T+3*n+8) := by
    have h := Nat.mul_le_mul_left T hfactor
    simpa only [Nat.mul_comm 7 T] using h
  have hsmallT : T<2^n := by
    change T*(3*T+3*n+8)<7*2^n at hSmall
    omega
  rcases hgate with hd5 | hEven
  · exact source_counted_no_low_budget_feeder n b d m z hn
      hcone hSmall (Or.inl hd5)
  · obtain ⟨t,k,c,hb,hmod,hinv,hk,heven,hreach⟩ := hEven
    by_cases hc0 : c=0
    · subst c
      have hneed := source_critical_zero_even_needs_exponential_reset_budget
        n b d m z t k hn hcone hb hmod hinv hk hreach
      omega
    · have hc : 2≤c := by omega
      exact source_counted_no_low_budget_feeder n b d m z hn
        hcone hSmall (Or.inr ⟨t,k,c,hb,hmod,hinv,hk,hc,heven,hreach⟩)

#print axioms BB6.Agent8Reset.source_no_low_budget_all_even_feeders
end BB6.Agent8Reset
