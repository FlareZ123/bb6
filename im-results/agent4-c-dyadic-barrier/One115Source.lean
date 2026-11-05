import OddOddLowVal
import EvenRightSixOrbit
import EvenOddFourExact
import Agent3COrbitIff
import Agent3CImage
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4One115
open BB6.Agent3 BB6.Agent46

/-- For all right counters k = 115 mod 128, the genuine Machine C blank
    section orbit never visits (1,k). This strengthens the single 115-mod-384
    raw-first-gate cylinder while avoiding any claim of a new halting gate.

    The forced source ancestors have exact forms, in order:
      (1,128*r+115) -> (64*r+56,96*r+84)
      -> (160*r+138,48*r+41) -> (104*r+87,76*r+63).
    The final point is outside the section source image by the already
    proved odd-output invariant. -/
theorem blank_no_one_115_mod128 (r : Nat) :
    ¬ BB6.Agent3.CReach 1 (128*r+115) := by
  intro hr
  have hP0 := (BB6.Agent3.oddodd_lowval_blank_reach_iff
    1 (128*r+115) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)).mp hr
  have hP : BB6.Agent3.CReach (64*r+56) (96*r+84) := by
    have hx : (1+(128*r+115)-4)/2=64*r+56 := by omega
    have hy : (1+3*(128*r+115)-10)/4=96*r+84 := by omega
    simpa only [hx,hy] using hP0
  have hQ0 := (BB6.Agent46.six_even_right_blank_reach_iff
    (64*r+56) (96*r+84) (by omega) (by omega)
    (by omega) (by omega)).mp hP
  have hQ : BB6.Agent3.CReach (160*r+138) (48*r+41) := by
    have hx : (64*r+56)+(96*r+84)-2=160*r+138 := by omega
    have hy : ((96*r+84)-2)/2=48*r+41 := by omega
    simpa only [hx,hy] using hQ0
  have hR0 := (BB6.Agent3.evenodd_four_blank_reach_iff
    (160*r+138) (48*r+41) (by omega) (by omega)
    (by omega) (by omega)).mp hQ
  have hR : BB6.Agent3.CReach (104*r+87) (76*r+63) := by
    have hx : ((160*r+138)+(48*r+41)-5)/2=104*r+87 := by omega
    have hy : ((160*r+138)+3*(48*r+41)-9)/4=76*r+63 := by omega
    simpa only [hx,hy] using hR0
  rcases hR with ⟨n,hn⟩
  cases n with
  | zero => simp [BB6.Agent8Section.run] at hn
  | succ n =>
    have hh := BB6.Agent3.blank_section_odd_image n
      (104*r+87) (76*r+63) hn (by omega) (by omega)
    omega

#print axioms blank_no_one_115_mod128
end BB6.Agent4One115
