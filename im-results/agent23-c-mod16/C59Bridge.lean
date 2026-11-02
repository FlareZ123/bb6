import C59
import CMod16Bridge
namespace BB6.Agent23

theorem source_reset_fiftynine_mod_sixtyfour_unreachable (t : Nat) :
    ¬BB6CLine.Reach (128*t+119,192*t+181,0) := by
  intro hr
  exact reset_fiftynine_mod_sixtyfour_unreachable t (reach_agree _ hr)

#print axioms source_reset_fiftynine_mod_sixtyfour_unreachable
end BB6.Agent23
