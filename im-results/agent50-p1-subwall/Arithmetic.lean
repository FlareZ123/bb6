import Lean

namespace BB6.Agent50Subwall

theorem subwall_arithmetic
    (n m z s m1 k b : Nat)
    (hlarge : 2*2^n ≤ k+4)
    (hdyadic : 2^s*(b+12)=2*(k+4))
    (hb : b ≤ 4*(m+n))
    (hcount : 2*z ≤ m1)
    (hcost : m=m1+s) :
    2^(n+2*z) ≤ 2^m*(m+n+3) := by
  have hnorm : b+12 ≤ 4*(m+n+3) := by omega
  have hpowBound : 2^s*(b+12) ≤ 2^s*(4*(m+n+3)) :=
    Nat.mul_le_mul_left (2^s) hnorm
  have hscale : 2^s*(4*(m+n+3)) = 4*(2^s*(m+n+3)) := by ac_rfl
  have htailBound : 2^n ≤ 2^s*(m+n+3) := by
    rw [hscale] at hpowBound
    omega
  have hpowMon : (2:Nat)^(2*z) ≤ 2^m1 :=
    Nat.pow_le_pow_right (by decide) hcount
  calc
    2^(n+2*z) = 2^(2*z)*2^n := by rw [Nat.pow_add]; ac_rfl
    _ ≤ 2^m1*(2^s*(m+n+3)) := Nat.mul_le_mul hpowMon htailBound
    _ = 2^m*(m+n+3) := by rw [hcost, Nat.pow_add]; ac_rfl

#print axioms BB6.Agent50Subwall.subwall_arithmetic
end BB6.Agent50Subwall
