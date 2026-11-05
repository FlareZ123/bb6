import CountedEnergySource

namespace BB6.Agent43CountedEnergy

open BB6.Agent28

/-- Exact conversion of the counted source energy envelope to a single dyadic
    exponent. This is pure Nat arithmetic. -/
theorem counted_energy_rhs_power (n z : Nat) :
    (16*2^n)*(8*2^n*2^n)^z =
      2^(n+4+(2*n+3)*z) := by
  have hbase : 8*2^n*2^n = 2^(2*n+3) := by
    calc
      8*2^n*2^n = (2^3)*(2^n)*(2^n) := by decide
      _ = 2^((3+n)+n) := by
        rw [Nat.pow_add, Nat.pow_add]
        ac_rfl
      _ = 2^(2*n+3) := by congr 1; omega
  have htop : 16*2^n = 2^(n+4) := by
    calc
      16*2^n = 2^4*2^n := by decide
      _ = 2^(4+n) := (Nat.pow_add 2 4 n).symm
      _ = 2^(n+4) := by congr 1; omega
  rw [hbase, htop]
  calc
    2^(n+4)*(2^(2*n+3))^z =
      2^(n+4)*2^((2*n+3)*z) := by rw [Nat.pow_mul]
    _ = 2^(n+4+(2*n+3)*z) :=
      (Nat.pow_add 2 (n+4) ((2*n+3)*z)).symm

/-- A genuine P1 critical counted inverse word cannot spend more than
    n+1+(2n+3) per positive-depth reset, regardless of word length. -/
theorem source_counted_cost_linear_in_resets
    (n b d m z : Nat) (hn : 14 ≤ n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z) :
    m ≤ n+1+(2*n+3)*z := by
  have henergy := source_counted_energy_bound n b d m z hn h
  have hscaled : 2^m*(b+12) ≤
      2^(n+4+(2*n+3)*z) := by
    rw [← counted_energy_rhs_power]
    exact henergy
  have hsmall : 2^(m+3) ≤ 2^m*(b+12) := by
    calc
      2^(m+3) = 2^m*2^3 := Nat.pow_add 2 m 3
      _ = 2^m*8 := by decide
      _ ≤ 2^m*(b+12) :=
        Nat.mul_le_mul_left (2^m) (by omega)
  have hpow : 2^(m+3) ≤ 2^(n+4+(2*n+3)*z) :=
    hsmall.trans hscaled
  by_contra hfail
  have hm : n+4+(2*n+3)*z < m+3 := by omega
  have hpStrict : (2:Nat)^(n+4+(2*n+3)*z) < 2^(m+3) :=
    Nat.pow_lt_pow_right (by decide) hm
  omega

/-- Source-certified high-cost escape must carry a correspondingly large
    count of positive resets. -/
theorem source_high_cost_requires_resets
    (n b d m z : Nat) (hn : 14 ≤ n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hhigh : 2^n ≤ m) :
    2^n ≤ n+1+(2*n+3)*z := by
  exact (hhigh.trans (source_counted_cost_linear_in_resets n b d m z hn h))

/-- An exact numerical instance at the genuine n=62 critical P1 precursor. -/
theorem source_high_cost_n62_many_resets
    (b d m z : Nat)
    (h : CountCone (14*2^62-2*62-16) 3 b d m z)
    (hhigh : 2^62 ≤ m) :
    36312488334073921 ≤ z := by
  have hcost := source_high_cost_requires_resets 62 b d m z
    (by decide) h hhigh
  have hp : (2:Nat)^62 = 4611686018427387904 := by decide
  rw [hp] at hcost
  omega

#print axioms BB6.Agent43CountedEnergy.counted_energy_rhs_power
#print axioms BB6.Agent43CountedEnergy.source_counted_cost_linear_in_resets
#print axioms BB6.Agent43CountedEnergy.source_high_cost_requires_resets
#print axioms BB6.Agent43CountedEnergy.source_high_cost_n62_many_resets

end BB6.Agent43CountedEnergy
