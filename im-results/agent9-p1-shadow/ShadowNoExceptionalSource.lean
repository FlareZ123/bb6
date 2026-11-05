import ShadowNoExceptionalGeneral
import ShadowDepthArithmetic
import P1InverseLog

namespace BB6.Shadow
open BB6.Agent47P1

/-- An exact original P1 inverse branch cannot have right coordinate one
when the shadow offset occupies fewer than J low bits and the source
cost leaves J+1 dyadic levels unused. This statement imports the unchanged
P1 inverseAt and its power identity; its cost and size conditions are explicit. -/
theorem source_no_exceptional_with_carry_gap
    (N L m J b d w z alpha t k : Nat)
    (hmass : b+d+2*m+2*L+3=56*2^N)
    (hoff : L+m=w+z)
    (henc : b+4*w=alpha*2^(N-m))
    (hb : b%2=0)
    (hz : 0<z)
    (hJ : 2≤J)
    (hbudget : m+J+1≤N)
    (hgap : 2*(L+m)<2^J)
    (hmasssmall : m+L≤2^N)
    (hi : inverseAt b d t=some (k,1)) : False := by
  have hsafe : m+(J-2)+3≤N := by omega
  have hdiv := encoded_shift_divisible
    N L m (J-2) b d w z alpha hmass hoff henc hb hsafe
  have hJnorm : (J-2)+2=J := by omega
  rw [hJnorm] at hdiv
  have hsmallz : 2*z<2^J := by omega
  have hpowle : 2^J≤2^N :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hshift : 2^J<d+b/2+3 := by
    have hbig := shifted_gt_power N L m b d hmass hmasssmall hb
    omega
  exact no_one_after_binary_gap J t (d+b/2+3) z hz hsmallz hdiv
    (inverseAt_power b d t k 1 hi) hshift

#print axioms source_no_exceptional_with_carry_gap
end BB6.Shadow
