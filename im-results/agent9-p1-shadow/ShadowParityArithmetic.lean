import ShadowDepthArithmetic
namespace BB6.Shadow

/-- Exact reduced right-counter quotient after factoring out an inverse depth. -/
theorem inverse_shadow_remainder (t Q c z s r : Nat)
    (h : s+2*z=2^(t+2)*Q)
    (h2 : s=2^t*(c+3))
    (hz : z=2^t*r) : c+3+2*r=4*Q := by
  have ha : 0<2^t := Nat.two_pow_pos t
  have hp : 2^(t+2)=2^t*4 := by rw [Nat.pow_add]
  have hexact : 2^t*(c+3+2*r)=2^t*(4*Q) := by
    calc
      2^t*(c+3+2*r) = s+2*z := by rw [h2,hz]; grind
      _ = 2^(t+2)*Q := h
      _ = 2^t*(4*Q) := by rw [hp, Nat.mul_assoc]
  exact Nat.mul_left_cancel ha hexact

/-- Exact parity classification for a source inverse output at depth t. -/
theorem odd_inverse_iff_divisible (t Q c z s : Nat)
    (h : s+2*z=2^(t+2)*Q)
    (h2 : s=2^t*(c+3)) :
    c%2=1 ↔ 2^t ∣ z := by
  constructor
  · intro hc
    exact odd_inverse_divisible t Q c z s h h2 hc
  · rintro ⟨r,hr⟩
    have hdiv := inverse_shadow_remainder t Q c z s r h h2 hr
    omega

/-- Exact mass plus reduced inverse counter constrains k's parity. -/
theorem parity_key (P E k Q r c b d t : Nat)
    (hmass : b+d+2*E+3=56*P)
    (hcost : 2*k+c+2*t+2=b+d)
    (hres : c+3+2*r=4*Q) :
    k+2*Q+E+t+1=28*P+r := by omega

/-- Even-child integrality is exactly the shadow numerator parity. -/
theorem parity_integral (P E k Q r t : Nat)
    (hk : 2≤k)
    (hkey : k+2*Q+E+t+1=28*P+r) :
    ((2*k-4)%4=0 ↔ (E+t+1+r)%2=0) := by omega

#print axioms inverse_shadow_remainder
#print axioms odd_inverse_iff_divisible
#print axioms parity_key
#print axioms parity_integral
end BB6.Shadow
