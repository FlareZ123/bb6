import OddOddLowVal
import EvenRightSixOrbit
import EvenOddFourExact
import Agent3COrbitIff
import Agent3CImage
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4One51
open BB6.Agent3 BB6.Agent46

/-- New uniform genuine-blank exclusion with four exact forced section
    predecessors. This excludes an M384-admitted low halting parameter
    class m=323 modulo 512 once combined with the stopping equation.

    (1,512q+51)
      <- (256q+24,384q+36)
      <- (640q+58,192q+17)
      <- (416q+35,304q+25)
      <- (360q+28,332q+25)
      <- impossible source image: odd right >=5, sum =1 modulo4.

    Each arrow is a complete original-source predecessor fiber, proved
    by the independently established exact predecessor iff theorems. -/
theorem blank_no_one_51_mod512 (q : Nat) :
    ¬ BB6.Agent3.CReach 1 (512*q+51) := by
  intro hr
  have hP0 := (BB6.Agent3.oddodd_lowval_blank_reach_iff
    1 (512*q+51) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)).mp hr
  have hP : BB6.Agent3.CReach (256*q+24) (384*q+36) := by
    have hx : (1+(512*q+51)-4)/2=256*q+24 := by omega
    have hy : (1+3*(512*q+51)-10)/4=384*q+36 := by omega
    simpa only [BB6.Agent3.CReach, hx,hy] using hP0
  have hQ0 := (BB6.Agent46.six_even_right_blank_reach_iff
    (256*q+24) (384*q+36) (by omega) (by omega)
    (by omega) (by omega)).mp hP
  have hQ : BB6.Agent3.CReach (640*q+58) (192*q+17) := by
    have hx : (256*q+24)+(384*q+36)-2=640*q+58 := by omega
    have hy : ((384*q+36)-2)/2=192*q+17 := by omega
    simpa only [hx,hy] using hQ0
  have hR0 := (BB6.Agent3.evenodd_four_blank_reach_iff
    (640*q+58) (192*q+17) (by omega) (by omega)
    (by omega) (by omega)).mp hQ
  have hR : BB6.Agent3.CReach (416*q+35) (304*q+25) := by
    have hx : ((640*q+58)+(192*q+17)-5)/2=416*q+35 := by omega
    have hy : ((640*q+58)+3*(192*q+17)-9)/4=304*q+25 := by omega
    simpa only [BB6.Agent3.CReach, hx,hy] using hR0
  have hS0 := (BB6.Agent3.oddodd_lowval_blank_reach_iff
    (416*q+35) (304*q+25) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)).mp hR
  have hS : BB6.Agent3.CReach (360*q+28) (332*q+25) := by
    have hx : ((416*q+35)+(304*q+25)-4)/2=360*q+28 := by omega
    have hy : ((416*q+35)+3*(304*q+25)-10)/4=332*q+25 := by omega
    simpa only [BB6.Agent3.CReach, hx,hy] using hS0
  rcases hS with ⟨n,hn⟩
  cases n with
  | zero => simp [BB6.Agent8Section.run] at hn
  | succ n =>
      have hh := BB6.Agent3.blank_section_odd_image n
        (360*q+28) (332*q+25) hn (by omega) (by omega)
      omega

/-- Infinite previously surviving first-family halting parameter cylinder.
    The original first halting equation connects m modulo 512 to the new
    source-proven unreachable right-counter cylinder, without any run bound. -/
theorem low_halt_m323_mod512_unreachable (m k : Nat)
    (hm : m%512=323)
    (hgate : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hm3 : 3≤m := by omega
  have hpow : 512 ∣ 2^(2*m+3) := by
    change 2^9 ∣ 2^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hmod : (k+3*m+4)%512=0 := by
    rw [hgate]
    exact Nat.mod_eq_zero_of_dvd hpow
  have hkmod : k%512=51 := by omega
  have hk : k=512*(k/512)+51 := by omega
  rw [hk]
  exact blank_no_one_51_mod512 (k/512)

#print axioms blank_no_one_51_mod512
#print axioms low_halt_m323_mod512_unreachable
end BB6.Agent4One51
