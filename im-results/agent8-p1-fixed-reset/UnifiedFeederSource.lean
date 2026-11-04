import ExceptionalBudgetSource
import P1ScalarBridge

namespace BB6.Agent8Reset
open BB6.Agent28 BB6.Agent1Quarter

/-- Genuine critical P1 odd inverse histories with small dyadic budgets
cannot contain either a c=1 exceptional odd terminal or a positive-even
exit whose predecessor is in the authentic blank-origin Reach relation.
This theorem does not cover c=0 or arbitrarily large reset budgets. -/
theorem source_counted_no_low_budget_feeder
    (n b d m z : Nat) (hn : 14 ≤ n)
    (hcone : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hSmall : budget (n+2) z*(3*budget (n+2) z+3*n+8) < 7*2^n)
    (hgate : d=5 ∨
      ∃ t k c : Nat,
        8≤b ∧ b%4=0 ∧ inverseAt b d t = some (k,c) ∧
        2≤k ∧ 2≤c ∧ c%2=0 ∧
        BB6.Agent1.Reach (2*k-4) (c+4)) :
    False := by
  let T := budget (n+2) z
  have hfactor : 7 ≤ 3*T+3*n+8 := by omega
  have htimes : 7*T ≤ T*(3*T+3*n+8) := by
    have h := Nat.mul_le_mul_left T hfactor
    simpa only [Nat.mul_comm 7 T] using h
  have hT : T < 2^n := by
    change T*(3*T+3*n+8) < 7*2^n at hSmall
    omega
  rcases hgate with hd5 | hEven
  · have hneed : 2^n ≤ T :=
      source_critical_d5_needs_exponential_reset_budget n b d m z hn hcone hd5
    omega
  · obtain ⟨t,k,c,hb,hmod,hinv,hk,hc,heven,hreach⟩ := hEven
    have hcost : m<n :=
      source_counted_cost_lt_exponent n b d m z hn hcone hT
    have hm : m ≤ 2^n := by
      have hp : 0 < (2:Nat)^n := Nat.pow_pos (by decide)
      omega
    have hodd : OddCone (14*2^n-2*n-16) 3 b d m :=
      counted_is_odd _ _ _ _ _ _ hcone
    obtain ⟨_,hwall⟩ :=
      BB6.Agent28Scalar.source_critical_low_cost_even_exit
        n b d m t k c (by omega) hodd hb hmod hm hinv hk hc heven hreach
    exact source_counted_no_wall_when_budget_small n b d m z hn hcone hwall hSmall

#print axioms BB6.Agent8Reset.source_counted_no_low_budget_feeder
end BB6.Agent8Reset
