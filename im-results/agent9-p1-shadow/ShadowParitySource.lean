import P1InverseLog
import MassInverse
import ShadowParityArithmetic

namespace BB6.Shadow
open BB6.Agent47P1
open BB6.Agent1Quarter

/-- Exact authentic output parity for a safely encoded P1 source inverseAt:
    the returned right coordinate is odd iff the offset z is divisible by 2^t. -/
theorem source_odd_iff_offset_dvd
    (N L m t b d w z alpha k c : Nat)
    (hmass : b+d+2*m+2*L+3 = 56*2^N)
    (hoff : L+m = w+z)
    (henc : b+4*w = alpha*2^(N-m))
    (hbeven : b%2=0)
    (hsafe : m+t+3 ≤ N)
    (hi : inverseAt b d t = some (k,c)) :
    c%2=1 ↔ 2^t ∣ z := by
  obtain ⟨Q,hQ⟩ := encoded_shift_divisible N L m t b d w z alpha
    hmass hoff henc hbeven hsafe
  exact odd_inverse_iff_divisible t Q c z (d+b/2+3) hQ
    (inverseAt_power b d t k c hi)

/-- An odd source inverse output gives a valid next odd hub iff the
    compressed shadow transition numerator has even parity. -/
theorem source_odd_child_iff_integral
    (N L m t b d w z alpha k c r : Nat)
    (hmass : b+d+2*m+2*L+3 = 56*2^N)
    (hoff : L+m = w+z)
    (henc : b+4*w = alpha*2^(N-m))
    (hb : 8≤b) (hb4 : b%4=0) (hd : d%2=1)
    (hsafe : m+t+3 ≤ N)
    (hi : inverseAt b d t = some (k,c))
    (hcodd : c%2=1)
    (hk : 2≤k)
    (hz : z=2^t*r) :
    ((2*k-4)%4=0 ↔ (L+m+t+1+r)%2=0) := by
  obtain ⟨Q,hQ⟩ := encoded_shift_divisible N L m t b d w z alpha
    hmass hoff henc (by omega) hsafe
  have hres := inverse_shadow_remainder t Q c z (d+b/2+3) r hQ
    (inverseAt_power b d t k c hi) hz
  have hcost := inverseAt_odd_cost b d t k c (by omega) hb4 hd hi hcodd
  have hkey := parity_key (2^N) (L+m) k Q r c b d t
    (by omega : b+d+2*(L+m)+3=56*2^N)
    (by omega : 2*k+c+2*t+2=b+d) hres
  exact parity_integral (2^N) (L+m) k Q r t hk hkey

#print axioms source_odd_iff_offset_dvd
#print axioms source_odd_child_iff_integral
end BB6.Shadow
