import ValSixSecondConeSource
import ValSixSecondHighArithmetic
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3ValSix

theorem high_second_cone_blank_unreachable (j m k:Nat)
    (hm:4≤m) (hj:j%128=81) (hpair:(j+63)%256=(3*m)%256)
    (hstop:k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  obtain ⟨hx,hy⟩ := second_cone_high_arithmetic j m k hm hj hpair hstop
  exact second_cone_blank_unreachable (2*j+3) k hx hy

#print axioms high_second_cone_blank_unreachable
end BB6.Agent3ValSix
