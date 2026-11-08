import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent50Density

/-- A parameterized bound with k an upper binary logarithm of n. -/
theorem log_budget_numeric (n k z : Nat) (hn : 14≤n)
    (hk : n≤2^k) (hsmall : 3*z+2*k+9≤n) :
    32*(2*n+7+(2*n+3)*z)*8^z≤2^n := by
  have hz : z≤n := by omega
  have hCoeff1 : 2*n+3≤3*n := by omega
  have hCoeff2 : 2*n+7≤3*n := by omega
  have hprod : (2*n+3)*z≤(3*n)*n := Nat.mul_le_mul hCoeff1 hz
  have hn1 : 1≤n := by omega
  have hnn : n≤n*n := by
    have hmul := Nat.mul_le_mul_left n hn1
    omega
  have h3nn : 3*n≤3*n*n := by
    have hmul := Nat.mul_le_mul_left 3 hnn
    simpa only [Nat.mul_assoc] using hmul
  have hCoef : 2*n+7+(2*n+3)*z ≤8*n*n := by
    have hprod' : (2*n+3)*z≤3*(n*n) := by
      simpa only [Nat.mul_assoc] using hprod
    have hcoef' : 2*n+7+(2*n+3)*z ≤8*(n*n) := by omega
    simpa only [Nat.mul_assoc] using hcoef'
  have hSquare : n*n≤2^k*2^k := Nat.mul_le_mul hk hk
  have hScale : 8*n*n≤8*(2^k*2^k) := by
    have hmul := Nat.mul_le_mul_left 8 hSquare
    simpa only [Nat.mul_assoc] using hmul
  have hCoeffPow : 2*n+7+(2*n+3)*z ≤ 8*(2^k*2^k) :=
    Nat.le_trans hCoef hScale
  have hMultiply := Nat.mul_le_mul_right (8^z)
    (Nat.mul_le_mul_left 32 hCoeffPow)
  have hIdentity : 32*(8*(2^k*2^k))*8^z=2^(8+2*k+3*z) := by
    have hkk : 2^k*2^k=2^(2*k) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have h8 : 8^z=2^(3*z) := by
      calc
        8^z = (2^3)^z := by congr
        _ = 2^(3*z) := (Nat.pow_mul 2 3 z).symm
    calc
      32*(8*(2^k*2^k))*8^z = 2^8*2^(2*k)*2^(3*z) := by
        rw [hkk,h8]
        have hc : 32*8=2^8 := by decide
        calc
          32*(8*2^(2*k))*2^(3*z) = (32*8)*2^(2*k)*2^(3*z) := by ac_rfl
          _ = 2^8*2^(2*k)*2^(3*z) := by rw [hc]
      _ = 2^(8+2*k+3*z) := by
        rw [Nat.pow_add, Nat.pow_add]
  have hExponent : 8+2*k+3*z≤n := by omega
  have hPpower : 2^(8+2*k+3*z)≤2^n :=
    Nat.pow_le_pow_right (by decide) hExponent
  calc
    32*(2*n+7+(2*n+3)*z)*8^z ≤ 32*(8*(2^k*2^k))*8^z := hMultiply
    _ = 2^(8+2*k+3*z) := hIdentity
    _ ≤ 2^n := hPpower

#print axioms BB6.Agent50Density.log_budget_numeric
end BB6.Agent50Density
