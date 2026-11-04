import ZeroThreePredecessor
import ZeroOneSource
import InverseIff
import OddConeMass

namespace BB6.Agent8Zero
open BB6.Agent1Quarter BB6.Agent47P1

theorem odd_cone_no_24_33
    (b0 d0 b d m : Nat) (hstart : b0 ≠ 24)
    (hcone : OddCone b0 d0 b d m) :
    ¬ (b=24 ∧ d=33) := by
  induction hcone with
  | root =>
      intro h
      exact hstart h.1
  | parent b d m t k c hprev hb hb4 hd hi hk hc ih =>
      rintro ⟨heqb,heqd⟩
      have hk14 : k=14 := by omega
      have hc29 : c=29 := by omega
      have hinv : inverseAt b d t = some (14,29) := by
        simpa [hk14,hc29] using hi
      obtain ⟨hp,hm⟩ := (inverseAt_iff_power_mass
        b d t 14 29 (by omega) hb4 hd).mp hinv
      have hp' : d+b/2+3=32*2^t := by
        simpa [Nat.mul_comm] using hp
      have hm' : b+d=59+2*t := by omega
      exact no_odd_parent_of_24_33 b d t hb hb4 hp' hm'

theorem odd_cone_no_100_17
    (b0 d0 b d m : Nat) (hstart : b0 ≠ 100)
    (hcone : OddCone b0 d0 b d m) :
    ¬ (b=100 ∧ d=17) := by
  induction hcone with
  | root =>
      intro h
      exact hstart h.1
  | parent b d m t k c hprev hb hb4 hd hi hk hc ih =>
      rintro ⟨heqb,heqd⟩
      have hk52 : k=52 := by omega
      have hc13 : c=13 := by omega
      have hinv : inverseAt b d t = some (52,13) := by
        simpa [hk52,hc13] using hi
      obtain ⟨hp,hm⟩ := (inverseAt_iff_power_mass
        b d t 52 13 (by omega) hb4 hd).mp hinv
      have hp' : d+b/2+3=16*2^t := by
        simpa [Nat.mul_comm] using hp
      have hm' : b+d=119+2*t := by omega
      exact no_odd_parent_of_100_17 b d t hb hb4 hp' hm'

theorem odd_cone_no_44_71
    (b0 d0 b d m : Nat) (hstart : b0 ≠ 44)
    (hstart100 : b0 ≠ 100)
    (hcone : OddCone b0 d0 b d m) :
    ¬ (b=44 ∧ d=71) := by
  induction hcone with
  | root =>
      intro h
      exact hstart h.1
  | parent b d m t k c hprev hb hb4 hd hi hk hc ih =>
      rintro ⟨heqb,heqd⟩
      have hk24 : k=24 := by omega
      have hc67 : c=67 := by omega
      have hinv : inverseAt b d t = some (24,67) := by
        simpa [hk24,hc67] using hi
      obtain ⟨hp,hm⟩ := (inverseAt_iff_power_mass
        b d t 24 67 (by omega) hb4 hd).mp hinv
      have hp' : d+b/2+3=70*2^t := by
        simpa [Nat.mul_comm] using hp
      have hm' : b+d=117+2*t := by omega
      obtain ⟨heqb',heqd',ht⟩ :=
        only_odd_parent_of_44_71 b d t hb hb4 hp' hm'
      exact (odd_cone_no_100_17 b0 d0 b d m hstart100 hprev)
        ⟨heqb',heqd'⟩

private theorem critical_root_gt_100 (n : Nat) (hn : 14≤n) :
    100 < 14*2^n-2*n-16 := by
  have hpow : (2:Nat)^14 ≤ 2^n :=
    Nat.pow_le_pow_right (by decide) hn
  have hp : n < (2:Nat)^n := Nat.lt_pow_self (by decide)
  have h14 : (2:Nat)^14=16384 := by decide
  rw [h14] at hpow
  omega

/-- The first three rigid zero-even feeder indices are universally impossible
    in original-source critical odd cones. -/
theorem source_critical_zero_even_index_at_least_four
    (n b d m t k : Nat) (hn : 14≤n)
    (hcone : OddCone (14*2^n-2*n-16) 3 b d m)
    (hb : 8≤b) (hb4 : b%4=0)
    (hinv : inverseAt b d t = some (k,0)) (hk : 2≤k)
    (hreach : BB6.Agent1.Reach (2*k-4) 4) :
    ∃ j : Nat, 4≤j ∧ j<n ∧
      t=j+2 ∧ b=4*(2^j+j) ∧
      d+2*j+3=10*2^j ∧
      7*2^j+n+m+j+5=7*2^n ∧
      3*2^n≤m := by
  obtain ⟨j,hj2,hjn,ht,hb',hd',hEq,hLarge⟩ :=
    source_critical_zero_even_index_at_least_two
      n b d m t k hn hcone hb hb4 hinv hk hreach
  have hgt := critical_root_gt_100 n hn
  have hnot24 := odd_cone_no_24_33
    (14*2^n-2*n-16) 3 b d m (by omega) hcone
  have hnot44 := odd_cone_no_44_71
    (14*2^n-2*n-16) 3 b d m (by omega) (by omega) hcone
  have hj4 : 4≤j := by
    by_cases h4 : 4≤j
    · exact h4
    · have h23 : j=2 ∨ j=3 := by omega
      rcases h23 with h2 | h3
      · have heq_b : b=24 := by simpa [h2] using hb'
        have heq_d : d=33 := by
          have heq : d+2*2+3=10*(2:Nat)^2 := by
            simpa [h2] using hd'
          omega
        exact False.elim (hnot24 ⟨heq_b,heq_d⟩)
      · have heq_b : b=44 := by simpa [h3] using hb'
        have heq_d : d=71 := by
          have heq : d+2*3+3=10*(2:Nat)^3 := by
            simpa [h3] using hd'
          omega
        exact False.elim (hnot44 ⟨heq_b,heq_d⟩)
  exact ⟨j,hj4,hjn,ht,hb',hd',hEq,hLarge⟩

#print axioms BB6.Agent8Zero.source_critical_zero_even_index_at_least_four
end BB6.Agent8Zero
