import Lean

namespace BB6.Shadow

/-- A universal polynomial certificate for the dyadic P1 inverse-shadow lift.
The hypotheses mirror source mass, inverse depth, parity and exact quotient
identities, but source imports are not yet part of this module. -/
theorem polynomial_step
  (X Y P alpha b d bh k c L m t z r zp : Int)
  (mass : b+d+2*m = 56*P-2*L-3)
  (coord : X*(b+4*(L+m-z)) = alpha*P)
  (half : b=2*bh)
  (inverse : Y*(c+3)=d+bh+3)
  (cost : 2*k+c+2*t+2=b+d)
  (division : z=Y*r)
  (next : 2*zp=L+m+t-1+r) :
  2*X*Y*((2*k-4)+4*(L+m+t+1-zp)) =
    (alpha+112*X*(Y-1))*P := by
  grind

#print axioms polynomial_step

/-- Pure arithmetic preservation of the four-unit shadow offset.
The r<z hypothesis for t>0 follows from positive dyadic division. -/
theorem offset_preserved
  (E z t r zp : Nat)
  (hE : 8 <= E) (hz : 0<z) (hw : z+4 <= E)
  (ht : (t=0 ∧ r=z) ∨ (0<t ∧ r<z))
  (hstep : 2*zp+1 = E+t+r) :
  0<zp ∧ zp+4<=E+t+1 := by
  rcases ht with hzero | hpos
  · rcases hzero with ⟨he, hr⟩
    subst t
    subst r
    omega
  · rcases hpos with ⟨ht,hr⟩
    omega

#print axioms offset_preserved

theorem strict_dyadic_remainder (z t r : Nat)
    (hz : 0<z) (ht : 0<t) (hdiv : z=2^t*r) : r<z := by
  have hr : 0<r := by
    by_cases he : r=0
    · simp [he] at hdiv
      omega
    · omega
  have hpow : 2 <= 2^t := by
    cases t with
    | zero => omega
    | succ t =>
      rw [Nat.pow_succ]
      have hp : 1 <= (2:Nat)^t := Nat.one_le_pow _ _ (by decide)
      omega
  have hb : 2*r <= 2^t*r := Nat.mul_le_mul_right r hpow
  omega

#print axioms strict_dyadic_remainder

/-- A full natural-number all-step theorem for the strict interior offset,
using exactly the integer dyadic quotient that the shadow graph enumerates. -/
theorem shadow_step_preserves_offset
  (L m z t r zp : Nat)
  (hL : 8 <= L) (hz : 0<z) (hw : z+4 <= L+m)
  (hdiv : z=2^t*r)
  (hnext : 2*zp+1=L+m+t+r) :
  0<zp ∧ zp+4<=L+m+t+1 := by
  have ht : (t=0 ∧ r=z) ∨ (0<t ∧ r<z) := by
    by_cases h : t=0
    · left
      constructor
      · exact h
      · simpa [h] using hdiv.symm
    · right
      constructor
      · omega
      · exact strict_dyadic_remainder z t r hz (by omega) hdiv
  exact offset_preserved (L+m) z t r zp (by omega) hz hw ht hnext

#print axioms shadow_step_preserves_offset
end BB6.Shadow


namespace BB6.Shadow

/-- Prime-power cancellation: the high 2-adic contribution cannot change
the exact odd core of twice z. No Mathlib imports or custom axioms. -/
theorem valuation_witness (v : Nat) (Q r s z : Int)
  (hz : z = (2:Int)^v*r)
  (hs : s+2*z = (2:Int)^(v+2)*Q)
  (hr : r%2=1) :
  s = (2:Int)^(v+1)*(2*Q-r) ∧ (2*Q-r)%2=1 := by
  constructor
  · rw [Int.pow_add] at hs
    rw [Int.pow_add]
    have htwo : (2:Int)^2=4 := by decide
    have hone : (2:Int)^1=2 := by decide
    rw [htwo] at hs
    rw [hone]
    grind
  · omega

#print axioms valuation_witness
end BB6.Shadow
