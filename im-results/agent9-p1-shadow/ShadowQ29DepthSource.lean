import ShadowDepthArithmetic
import ShadowCast
import ShadowQ29DepthArithmetic
import P1InverseLog

namespace BB6.Shadow
open BB6.Agent47P1

/-- Any genuine P1 inverse branch at a safely encoded q29-style
    shadow hub has depth at most eight when z is not divisible by 256.
    This bound is independent of the depth being bounded in advance. -/
theorem source_depth_le8_mod256
    (N L m b d w z alpha t k c : Nat)
    (hmass : b+d+2*m+2*L+3=56*2^N)
    (hoff : L+m=w+z)
    (hcoord : 2^m*(b+4*w)=alpha*2^N)
    (hbeven : b%2=0)
    (hbudget : m+11≤N)
    (hno256 : ¬256 ∣ z)
    (hi : inverseAt b d t=some (k,c)) :
    t≤8 := by
  have henc := unscale_coordinate N m b w alpha (by omega) hcoord
  have hbase := encoded_shift_divisible N L m 8 b d w z alpha
    hmass hoff henc hbeven (by omega)
  have hsub : 2^9 ∣ 2^10 := Nat.pow_dvd_pow 2 (by omega)
  have hmod : 2^9 ∣ d+b/2+3+2*z := dvd_trans hsub hbase
  exact q29_depth_modular t (d+b/2+3) z c
    hmod (inverseAt_power b d t k c hi) hno256

#print axioms source_depth_le8_mod256
end BB6.Shadow
