import ShadowDepthBudgetArithmetic
import ShadowDepthArithmetic
import ShadowCast
import P1InverseLog

namespace BB6.Agent9Budget
open BB6.Shadow BB6.Agent47P1

/-- At a genuinely encoded P1 inverse hub, excluding a power-of-two
    divisor of the shadow coordinate bounds every original inverse depth.
    Both K and the 2-adic modulus are parameters. -/
theorem source_depth_le_K
    (K N L m b d w z alpha t k c : Nat)
    (hmass : b+d+2*m+2*L+3=56*2^N)
    (hoff : L+m=w+z)
    (hcoord : 2^m*(b+4*w)=alpha*2^N)
    (hbeven : b%2=0)
    (hbudget : m+K+3≤N)
    (hnodiv : ¬2^K ∣ z)
    (hi : inverseAt b d t=some (k,c)) :
    t≤K := by
  have henc := unscale_coordinate N m b w alpha (by omega) hcoord
  have hbase := encoded_shift_divisible N L m K b d w z alpha
    hmass hoff henc hbeven (by omega)
  have hsub : 2^(K+1) ∣ 2^(K+2) := Nat.pow_dvd_pow 2 (by omega)
  have hmod : 2^(K+1) ∣ d+b/2+3+2*z := Nat.dvd_trans hsub hbase
  exact depth_le_of_dyadic_shadow K t (d+b/2+3) z c
    hmod (inverseAt_power b d t k c hi) hnodiv

#print axioms source_depth_le_K
end BB6.Agent9Budget
