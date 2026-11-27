import RationalShadow211
import U5AffineHighStop
import Lean.Elab.Tactic.Omega
namespace BB6.Agent15RationalShadow211
open BB6.Agent3

theorem u5_shadow_high_stop_excluded (f w s m : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m) (hc : u5Check f w=true) :
    ¬ CReach (2*(39+64*s)+3) (3*(39+64*s)+7) := by
  have hp : m+1=8*(m/8)+1 := by omega
  have hid := BB6.Agent3U5M16Residual.u5_m8_t_identity w s m (m/8) hs hm hp
  obtain ⟨n,ht,_⟩ := BB6.Agent15U5Affine.residual_index w (m/8) hid
  exact BB6.Agent15U5Affine.high_stop_excluded_of_x w s m hs hm
    (u5_shadow_x_excluded f w (m/8) (by omega) hid hc)

#print axioms u5_shadow_high_stop_excluded
end BB6.Agent15RationalShadow211
