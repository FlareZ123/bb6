import MixedFourNormalize
import Agent3CImage
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Every m=1 high stopping input with j=32q+1 has a forced odd/odd
    parent and then a forced even-right parent. The latter's sum is 1
    modulo four with large odd right counter, impossible after blank. -/
theorem mixed_high_m1_j_one_mod32_unreachable (q : Nat) :
    ¬ CReach (64*q+5) (480*q+55) := by
  intro hr
  have h1 : CReach (272*q+28) (376*q+40) := by
    have hp := (oddodd_lowval_blank_reach_iff (64*q+5) (480*q+55)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).mp hr
    have hx : ((64*q+5)+(480*q+55)-4)/2=272*q+28 := by omega
    have hy : ((64*q+5)+3*(480*q+55)-10)/4=376*q+40 := by omega
    simpa only [hx,hy] using hp
  have h2 : CReach (648*q+66) (188*q+19) := by
    have hp := (six_even_right_blank_reach_iff (272*q+28) (376*q+40)
      (by omega) (by omega) (by omega) (by omega)).mp h1
    have hx : (272*q+28)+(376*q+40)-2=648*q+66 := by omega
    have hy : ((376*q+40)-2)/2=188*q+19 := by omega
    simpa only [hx,hy] using hp
  rcases h2 with ⟨time,hn⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at hn
  | succ t =>
      have hi := blank_section_odd_image t (648*q+66) (188*q+19)
        hn (by omega) (by omega)
      omega

#print axioms mixed_high_m1_j_one_mod32_unreachable
end BB6.Agent3
