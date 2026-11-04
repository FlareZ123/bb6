import EvenChildSevenFour
import AffineNormalize
import SectionParam
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- An actual immediate stopping input of the unchanged Machine C
    section, at every member of an unbounded arithmetic progression. -/
theorem m1_tower_halt_input (t : Nat) :
    secNext (128*t+55,960*t+430)=none := by
  apply (BB6.Agent15.section_halts_iff_parametric _ _).mpr
  right
  right
  refine ⟨64*t+26,1,by omega,?_⟩
  change (960*t+430)+(64*t+26)+3*1+5 = 16*((64*t+26)+3)
  omega

/-- Three genuine and unique original-source affine predecessors
    reduce the entire halting family to the section cone whose
    predecessor ancestry has depth at most one. -/
theorem m1_tower_three_inverse (t : Nat) :
    BB6.Agent15.CReach (128*t+55) (960*t+430) ↔
    BB6.Agent15.CReach (1808*t+799) (120*t+52) := by
  have h1 : BB6.Agent15.CReach (128*t+55) (960*t+430) ↔
      BB6.Agent15.CReach (1088*t+483) (480*t+214) := by
    have h := BB6.Agent15.blank_reach_iff_affine (128*t+55) (960*t+430)
      (by omega) (by omega) (by omega)
    simpa only [BB6.Agent15.CReach,
      show 128*t+55+(960*t+430)-2=1088*t+483 by omega,
      show (960*t+430-2)/2=480*t+214 by omega] using h
  have h2 : BB6.Agent15.CReach (1088*t+483) (480*t+214) ↔
      BB6.Agent15.CReach (1568*t+695) (240*t+106) := by
    have h := BB6.Agent15.blank_reach_iff_affine (1088*t+483) (480*t+214)
      (by omega) (by omega) (by omega)
    simpa only [BB6.Agent15.CReach,
      show 1088*t+483+(480*t+214)-2=1568*t+695 by omega,
      show (480*t+214-2)/2=240*t+106 by omega] using h
  have h3 : BB6.Agent15.CReach (1568*t+695) (240*t+106) ↔
      BB6.Agent15.CReach (1808*t+799) (120*t+52) := by
    have h := BB6.Agent15.blank_reach_iff_affine (1568*t+695) (240*t+106)
      (by omega) (by omega) (by omega)
    simpa only [BB6.Agent15.CReach,
      show 1568*t+695+(240*t+106)-2=1808*t+799 by omega,
      show (240*t+106-2)/2=120*t+52 by omega] using h
  exact h1.trans (h2.trans h3)

/-- This infinite family of immediate stopping states is never visited
    by the true Machine C blank-start section. Each original target
    is nevertheless admitted by the B8/M32 finite quotient. -/
theorem m1_tower_blank_unreachable (t : Nat) :
    ¬ BB6.Agent15.CReach (128*t+55) (960*t+430) := by
  intro hr
  obtain ⟨n,hn⟩ := (m1_tower_three_inverse t).mp hr
  exact (seven_four_blank_unreachable n (1808*t+799) (120*t+52)
    (by omega) (by omega) (by omega)) hn

#print axioms m1_tower_halt_input
#print axioms m1_tower_three_inverse
#print axioms m1_tower_blank_unreachable

end BB6.Agent3
