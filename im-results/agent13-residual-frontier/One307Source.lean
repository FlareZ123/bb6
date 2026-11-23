import EvenOddSimpleRectangle
import OddOddLowVal
import EvenOddFourExact
import EvenRightSixOrbit
import Lean.Elab.Tactic.Omega

namespace BB6.Agent13One307
open BB6.Agent46 BB6.Agent3

/-- A new, original-source infinite low-target nonreachability cylinder:
    when the low target has shape (1,256*u+51) with u=49 mod128, its four
    forced exact predecessors land in a proven two-parent forbidden
    residue rectangle. No finite orbit cutoff and no quotient is used. -/
theorem no_one_256u51_u49_mod128
    (u : Nat) (hu : u%128=49) :
    ¬ BB6.Agent3.CReach 1 (256*u+51) := by
  have hR : ¬ BB6.Agent3.CReach (180*u+28) (166*u+25) := by
    apply BB6.Agent13SourceRect.even_odd_rectangle_144_223
    · omega
    · omega
  intro hr
  have hO1 := (BB6.Agent3.oddodd_lowval_blank_reach_iff
    1 (256*u+51) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)).mp hr
  have h1 : BB6.Agent3.CReach (128*u+24) (192*u+36) := by
    simpa only [BB6.Agent3.CReach,
      show (1+(256*u+51)-4)/2=128*u+24 by omega,
      show (1+3*(256*u+51)-10)/4=192*u+36 by omega] using hO1
  have hB := (BB6.Agent46.six_even_right_blank_reach_iff
    (128*u+24) (192*u+36)
    (by omega) (by omega) (by omega) (by omega)).mp h1
  have h2 : BB6.Agent3.CReach (320*u+58) (96*u+17) := by
    simpa only [BB6.Agent3.CReach,
      show (128*u+24)+(192*u+36)-2=320*u+58 by omega,
      show ((192*u+36)-2)/2=96*u+17 by omega] using hB
  have hF := (BB6.Agent3.evenodd_four_blank_reach_iff
    (320*u+58) (96*u+17)
    (by omega) (by omega) (by omega) (by omega)).mp h2
  have h3 : BB6.Agent3.CReach (208*u+35) (152*u+25) := by
    simpa only [BB6.Agent3.CReach,
      show ((320*u+58)+(96*u+17)-5)/2=208*u+35 by omega,
      show ((320*u+58)+3*(96*u+17)-9)/4=152*u+25 by omega] using hF
  have hO4 := (BB6.Agent3.oddodd_lowval_blank_reach_iff
    (208*u+35) (152*u+25)
    (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)).mp h3
  have h4 : BB6.Agent3.CReach (180*u+28) (166*u+25) := by
    simpa only [BB6.Agent3.CReach,
      show ((208*u+35)+(152*u+25)-4)/2=180*u+28 by omega,
      show ((208*u+35)+3*(152*u+25)-10)/4=166*u+25 by omega]
      using hO4
  exact hR h4

#print axioms no_one_256u51_u49_mod128
end BB6.Agent13One307
