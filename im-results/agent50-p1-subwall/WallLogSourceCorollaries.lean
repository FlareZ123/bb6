import WallLogNumeric
import WallResetDensitySource
import DepthIndexedResetFloor

namespace BB6.Agent50Density
open BB6.Agent28 BB6.Agent43DepthResetFloor

private theorem square_le_pow (n : Nat) (hn : 4≤n) : n*n≤2^n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn4 : 4≤n
    · have hprev := ih hn4
      have hpoly : (n+1)*(n+1)≤2*(n*n) := by
        have hn1 : 1≤n := by omega
        have hnn : n≤n*n := by
          have hmul := Nat.mul_le_mul_left n hn1
          omega
        have h4n : 4*n≤n*n := Nat.mul_le_mul_right n hn4
        simp only [Nat.mul_add, Nat.add_mul]
        omega
      rw [Nat.pow_succ]
      omega
    · have hEq : n=3 := by omega
      subst n
      decide

/-- Uniform logarithmic-correction reset floor for genuine P1 wall histories:
for every k with n≤2^k, the inequality n < 3z+2k+9 holds. -/
theorem source_log_wall_reset_floor
    (n k b d m z : Nat) (hn : 14≤n) (hk : n≤2^k)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hwall : b+4*m+4*n+20=12*2^n) :
    n<3*z+2*k+9 := by
  by_cases hg : n<3*z+2*k+9
  · exact hg
  · have hsmall : 3*z+2*k+9≤n := by omega
    have hNumeric := log_budget_numeric n k z hn hk hsmall
    have hGrowth := source_wall_reset_growth n b d m z hn h hwall
    omega

/-- The original-source right-five inverse histories, at any cost and any
positive-reset count, satisfy the nearly n/3 reset floor n < 3z+2k+9.
In particular k=ceil(log2 n) is admissible. -/
theorem source_log_right_five_reset_floor
    (n k b m z : Nat) (hn : 14≤n) (hk : n≤2^k)
    (h : CountCone (14*2^n-2*n-16) 3 b 5 m z) :
    n<3*z+2*k+9 := by
  rcases source_right_five_depth_reset_dichotomy n b m z hn h with
    hHigh | hPrefix
  · by_cases hz : n<3*z+2*k+9
    · exact hz
    · have hsmall : 3*z+2*k+9≤n := by omega
      have hzBound : z≤n := by omega
      have hSquare := square_le_pow n (by omega)
      have hProd := Nat.mul_le_mul_left (2*n+3) hzBound
      have h4n : 4*n≤n*n := Nat.mul_le_mul_right n (by omega)
      have hRewrite : (2*n+3)*n=2*(n*n)+3*n := by
        simp only [Nat.add_mul, Nat.mul_assoc]
      have hStrict : (2*n+3)*n <3*(n*n) := by rw [hRewrite]; omega
      have hPow3 : 3*(n*n)≤3*2^n := Nat.mul_le_mul_left 3 hSquare
      omega
  · rcases hPrefix with ⟨bp,dp,mp,zp,k0,hpre,hzEq,hzp,hip,hb,hkm,
        hbpExact,hwall,hdpExact,hmEq,hcost⟩
    have hPrefixFloor := source_log_wall_reset_floor
      n k bp dp mp zp hn hk hpre hwall
    omega


/-- Explicit near one-third bound using the binary logarithm: all original
right-five histories satisfy n < 3z+2*log2(n)+11. -/
theorem source_right_five_log_explicit
    (n b m z : Nat) (hn : 14≤n)
    (h : CountCone (14*2^n-2*n-16) 3 b 5 m z) :
    n < 3*z+2*Nat.log2 n+11 := by
  have hk : n≤2^(Nat.log2 n+1) :=
    Nat.le_of_lt (Nat.lt_log2_self (n:=n))
  have hbound := source_log_right_five_reset_floor
    n (Nat.log2 n+1) b m z hn hk h
  omega

#print axioms BB6.Agent50Density.source_log_wall_reset_floor
#print axioms BB6.Agent50Density.source_log_right_five_reset_floor
#print axioms BB6.Agent50Density.source_right_five_log_explicit
end BB6.Agent50Density
