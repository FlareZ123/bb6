import P1InverseLog
import ShadowDepthArithmetic

namespace BB6.Shadow
open BB6.Agent47P1

/-- Every authentic odd-right P1 inverse exit from a safely encoded
    dyadic shadow hub has depth bounded by the 2-adic content of z.
    The original inverseAt definition and its exact power theorem are imported. -/
theorem source_odd_depth_divides_offset
    (N L m t b d w z alpha k c : Nat)
    (hmass : b+d+2*m+2*L+3 = 56*2^N)
    (hoff : L+m = w+z)
    (henc : b+4*w = alpha*2^(N-m))
    (hbeven : b%2=0)
    (hsafe : m+t+3 ≤ N)
    (hi : inverseAt b d t = some (k,c))
    (hcodd : c%2=1) :
    2^t ∣ z := by
  obtain ⟨Q, hQ⟩ := encoded_shift_divisible N L m t b d w z alpha
    hmass hoff henc hbeven hsafe
  exact odd_inverse_divisible t Q c z (d+b/2+3) hQ
    (inverseAt_power b d t k c hi) hcodd

/-- All odd-right original inverseAt branches beyond the shadow
    2-adic depth are excluded, under exact encoding and safe-depth hypotheses. -/
theorem source_no_odd_depth_if_nondivisible
    (N L m t b d w z alpha k c : Nat)
    (hmass : b+d+2*m+2*L+3 = 56*2^N)
    (hoff : L+m = w+z)
    (henc : b+4*w = alpha*2^(N-m))
    (hbeven : b%2=0)
    (hsafe : m+t+3 ≤ N)
    (hnotdvd : ¬ 2^t ∣ z)
    (hi : inverseAt b d t = some (k,c)) :
    c%2 ≠ 1 := by
  intro hc
  exact hnotdvd (source_odd_depth_divides_offset N L m t b d w z alpha k c
    hmass hoff henc hbeven hsafe hi hc)

#print axioms source_odd_depth_divides_offset
#print axioms source_no_odd_depth_if_nondivisible
end BB6.Shadow
