import ValSixSource
import ValSixHighArithmetic
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3ValSix

/-- Infinite authentic Machine C high-stopping index family: none can
be reached from the genuine blank section seed (5,1). -/
theorem high_val_six_blank_unreachable (j m k : Nat)
    (hm : 4≤m) (hm8 : m%8=4)
    (hpair : (j+191)%256=(3*m)%256)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  obtain ⟨hx,hy,hsize,hmod,hbig⟩ :=
    high_val_six_arithmetic j m k hm hm8 hpair hstop
  exact val_six_blank_unreachable (2*j+3) k hx hy hsize hmod hbig

#print axioms high_val_six_blank_unreachable
end BB6.Agent3ValSix
