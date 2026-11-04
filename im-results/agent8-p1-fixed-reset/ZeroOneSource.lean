import ZeroOnePredecessor
import ZeroEvenExactSource
import InverseIff
import OddConeMass

namespace BB6.Agent8Zero
open BB6.Agent1Quarter BB6.Agent47P1

theorem odd_cone_no_12_19
    (b0 d0 b d m : Nat) (hstart : b0 ≠ 12)
    (hcone : OddCone b0 d0 b d m) :
    ¬ (b=12 ∧ d=19) := by
  induction hcone with
  | root =>
      intro h
      exact hstart h.1
  | parent b d m t k c hprev hb hb4 hd hi hk hc ih =>
      rintro ⟨heqb,heqd⟩
      have hk8 : k=8 := by omega
      have hc15 : c=15 := by omega
      have hinv : inverseAt b d t = some (8,15) := by
        simpa [hk8,hc15] using hi
      obtain ⟨hp,hm⟩ := (inverseAt_iff_power_mass
        b d t 8 15 (by omega) hb4 hd).mp hinv
      have hp' : d+b/2+3=18*2^t := by
        simpa [Nat.mul_comm] using hp
      have hm' : b+d=33+2*t := by omega
      exact no_odd_parent_of_12_19 b d t hb hb4 hp' hm'

theorem odd_cone_no_12_15
    (b0 d0 b d m : Nat) (hstart : b0 ≠ 12)
    (hcone : OddCone b0 d0 b d m) :
    ¬ (b=12 ∧ d=15) := by
  induction hcone with
  | root =>
      intro h
      exact hstart h.1
  | parent b d m t k c hprev hb hb4 hd hi hk hc ih =>
      rintro ⟨heqb,heqd⟩
      have hk8 : k=8 := by omega
      have hc11 : c=11 := by omega
      have hinv : inverseAt b d t = some (8,11) := by
        simpa [hk8,hc11] using hi
      obtain ⟨hp,hm⟩ := (inverseAt_iff_power_mass
        b d t 8 11 (by omega) hb4 hd).mp hinv
      have hp' : d+b/2+3=14*2^t := by
        simpa [Nat.mul_comm] using hp
      have hm' : b+d=29+2*t := by omega
      obtain ⟨heq_b,heq_d,heq_t⟩ :=
        only_odd_parent_of_12_15 b d t hb hb4 hp' hm'
      exact (odd_cone_no_12_19 b0 d0 b d m hstart hprev)
        ⟨heq_b,heq_d⟩

private theorem critical_root_not_12 (n : Nat) (hn : 14≤n) :
    14*2^n-2*n-16 ≠ 12 := by
  have hp : n < (2:Nat)^n := Nat.lt_pow_self (by decide)
  omega

theorem source_critical_zero_even_index_at_least_two
    (n b d m t k : Nat) (hn : 14≤n)
    (hcone : OddCone (14*2^n-2*n-16) 3 b d m)
    (hb : 8≤b) (hb4 : b%4=0)
    (hinv : inverseAt b d t = some (k,0)) (hk : 2≤k)
    (hreach : BB6.Agent1.Reach (2*k-4) 4) :
    ∃ j : Nat, 2≤j ∧ j<n ∧
      t=j+2 ∧ b=4*(2^j+j) ∧
      d+2*j+3=10*2^j ∧
      7*2^j+n+m+j+5=7*2^n ∧
      3*2^n≤m := by
  obtain ⟨j,hjn,ht,hb',hd',hEq,hCost,hLarge⟩ :=
    source_critical_zero_even_exact_cost n b d m t k hn hcone
      hb hb4 hinv hk hreach
  have hnot := odd_cone_no_12_15
    (14*2^n-2*n-16) 3 b d m (critical_root_not_12 n hn) hcone
  have hj : 2≤j := by
    by_cases h2 : 2≤j
    · exact h2
    · have h01 : j=0 ∨ j=1 := by omega
      rcases h01 with h0 | h1
      · have hsmall : b=4 := by simpa [h0] using hb'
        omega
      · have heq_b : b=12 := by simpa [h1] using hb'
        have heq_d : d=15 := by
          have h13 : d+2*1+3=10*(2:Nat)^1 := by simpa [h1] using hd'
          omega
        exact False.elim (hnot ⟨heq_b,heq_d⟩)
  exact ⟨j,hj,hjn,ht,hb',hd',hEq,hLarge⟩

#print axioms BB6.Agent8Zero.source_critical_zero_even_index_at_least_two
end BB6.Agent8Zero
