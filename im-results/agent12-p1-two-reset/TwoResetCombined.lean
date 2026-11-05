import FirstResetDefect
import SecondResetBudget
import OneResetSourceBudget
set_option maxRecDepth 4096
set_option maxHeartbeats 20000000

namespace BB6.Agent12TwoReset
open BB6.Agent28

/-- All exact normalized root upper / reset / upper / reset / upper
    critical P1 inverse words are excluded from the affine wall when n>=46.
    A separate original OddCone decomposition bridge is required to lift this
    to the original source inverse-cone quantifier. -/
theorem exact_two_reset_wall_impossible
    (n r l s ell u K Fr Dr Dp F1 D1 D2 F2 : Nat)
    (hn : 46≤n) (hl : 2≤l) (hell : 2≤ell)
    (hK : K+n+3=7*2^n)
    (hroot : 2^r*Fr+(n+2)=7*2^n)
    (hpre : Fr+Dr+r=K+2)
    (hreset1 : 2^l*Dp+r=K+Dr)
    (hpost1 : 2^s*F1+Dp+r+l=K+2)
    (hpre2 : F1+D1+(r+l+s)=K+2)
    (hreset2 : 2^ell*D2+(r+l+s)=K+D1)
    (hpost2 : 2^u*F2+D2+(r+l+s)+ell=K+2)
    (hwall : 7*2^n ≤ n+4+2^(r+l+s+ell+u)*
      (3*(r+l+s+ell+u)+2*n+4)) : False := by
  have hweight := exact_one_reset_word_polynomial_budget n r l s K Fr Dr Dp F1
    (by omega) hl hK hroot hpre hreset1 hpost1
  obtain ⟨C,N,hC,hNpos,hNbound,hdefect⟩ :=
    first_reset_has_positive_defect n r l s K Fr Dr Dp F1 hn hl
    hK hroot hpre hreset1 hpost1 hweight
  exact second_reset_forbids_wall n (r+l+s) ell u K F1 D1 D2 F2 C N
    hn hell hK hweight hC hNpos hNbound hdefect hpre2 hreset2 hpost2
    (by simpa only [Nat.add_assoc] using hwall)

#print axioms exact_two_reset_wall_impossible
end BB6.Agent12TwoReset
