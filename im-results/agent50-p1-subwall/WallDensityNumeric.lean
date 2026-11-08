import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent50Density

private theorem quad_bound (q : Nat) (hq : 17≤q) :
    32*(8*q*q+17*q+13) ≤ 2^q := by
  induction q with
  | zero => omega
  | succ q ih =>
    by_cases hq17 : 17≤q
    · have hprev := ih hq17
      have hpoly : 8*(q+1)*(q+1)+17*(q+1)+13 ≤
          2*(8*q*q+17*q+13) := by
        simp only [Nat.mul_add, Nat.add_mul]
        omega
      have hscale := Nat.mul_le_mul_left 32 hpoly
      rw [Nat.pow_succ]
      omega
    · have heq : q=16 := by omega
      subst q
      decide

/-- The homogeneous polynomial times 8^(n/4) stays below 2^n for n≥68. -/
theorem quarter_numeric (n : Nat) (hn : 68≤n) :
    32*(2*n+7+(2*n+3)*(n/4))*8^(n/4) ≤2^n := by
  let q := n/4
  have hq : 17≤q := by dsimp [q]; omega
  have hbound : n≤4*q+3 := by dsimp [q]; omega
  have hbelow : 4*q≤n := by dsimp [q]; omega
  have hc : 2*n+7+(2*n+3)*q ≤8*q*q+17*q+13 := by
    have h1 : 2*n+3≤8*q+9 := by omega
    have hm := Nat.mul_le_mul_right q h1
    simp only [Nat.add_mul] at *
    omega
  have hquad := quad_bound q hq
  have hmul1 : 32*(2*n+7+(2*n+3)*q)*8^q ≤
      32*(8*q*q+17*q+13)*8^q :=
    Nat.mul_le_mul_right (8^q) (Nat.mul_le_mul_left 32 hc)
  have hmul2 : 32*(8*q*q+17*q+13)*8^q ≤ 2^q*8^q :=
    Nat.mul_le_mul_right (8^q) hquad
  have hmulPow : 2^q*8^q=2^(4*q) := by
    calc
      2^q*8^q=(2*8)^q := (Nat.mul_pow 2 8 q).symm
      _=(2^4)^q := by congr
      _=2^(4*q) := (Nat.pow_mul 2 4 q).symm
  have hpow2 : 2^(4*q)≤2^n := Nat.pow_le_pow_right (by decide) hbelow
  have htotal : 32*(2*n+7+(2*n+3)*q)*8^q ≤ 2^n := by
    calc
      _ ≤ 32*(8*q*q+17*q+13)*8^q := hmul1
      _ ≤ 2^q*8^q := hmul2
      _ = 2^(4*q) := hmulPow
      _ ≤ 2^n := hpow2
  simpa only [q] using htotal

/-- The exponential reset-growth inequality forces more than a quarter of n
positive inverse resets for every n≥68. -/
theorem quarter_reset_from_growth (n z : Nat) (hn : 68≤n)
    (hg : 2^n < 32*(2*n+7+(2*n+3)*z)*8^z) :
    n/4 < z := by
  by_cases hz : n/4 < z
  · exact hz
  · have hle : z≤n/4 := by omega
    have hc : 2*n+7+(2*n+3)*z ≤
        2*n+7+(2*n+3)*(n/4) := by
      have hprod := Nat.mul_le_mul_left (2*n+3) hle
      omega
    have hpow : 8^z≤8^(n/4) := Nat.pow_le_pow_right (by decide) hle
    have hmult := Nat.mul_le_mul hc hpow
    have hbound : 32*(2*n+7+(2*n+3)*z)*8^z ≤
        32*(2*n+7+(2*n+3)*(n/4))*8^(n/4) := by
      have hscale := Nat.mul_le_mul_left 32 hmult
      simpa only [Nat.mul_assoc] using hscale
    have hnum := quarter_numeric n hn
    omega

#print axioms BB6.Agent50Density.quarter_numeric
#print axioms BB6.Agent50Density.quarter_reset_from_growth
end BB6.Agent50Density
