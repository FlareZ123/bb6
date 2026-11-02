import C7
import CMod16Bridge
namespace BB6.Agent23

theorem source_reset_seven_mod_sixtyfour_unreachable (t : Nat) :
    ¬BB6CLine.Reach (128*t+15,192*t+25,0) := by
  intro hr
  exact reset_seven_mod_sixtyfour_unreachable t (reach_agree _ hr)

#print axioms source_reset_seven_mod_sixtyfour_unreachable
end BB6.Agent23
