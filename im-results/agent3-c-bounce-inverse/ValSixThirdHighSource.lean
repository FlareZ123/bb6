import ValSixThirdConeSource
import ValSixThirdHighArithmetic
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3ValSix

/-- A third infinite authentic Machine C high-stopping candidate family
is absent from the genuine blank section, for every natural parameter. -/
theorem high_third_cone_blank_unreachable (j m k:Nat)
    (hm:4≤m) (hj:j%32=1) (hpair:(j+63)%256=(3*m)%256)
    (hstop:k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  obtain ⟨hy,hmod⟩ := third_cone_high_arithmetic j m k hm hj hpair hstop
  exact third_cone_blank_unreachable (2*j+3) k hy hmod

#print axioms high_third_cone_blank_unreachable
end BB6.Agent3ValSix
