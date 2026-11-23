import EvenOddLowStopDivisor
import EvenOddTwoParentRoot
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace BB6.Agent13LowEvenRoot
open BB6.Agent46

/-- For every even low-stop index z, the exact original-source inverse
    fan above R_u collapses to ONE possible parent, at bounce depth n=0.
    This holds for every (unbounded) z and every blank time, without
    a quotient, finite sample or arbitrary depth cutoff. -/
theorem even_low_ray_reach_forces_unique_parent
    (z u : Nat)
    (hu : u+6*z+1=2^(1024*z+129))
    (hz : z%2=0)
    (hr : BB6.Agent3.CReach (180*u+28) (166*u+25)) :
    BB6.Agent3.CReach (173*u+24) ((339*u+47)/2) := by
  obtain ⟨a,k,hpre,hedge⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      (180*u+28) (166*u+25) (by omega) hr
  obtain ⟨n,hn,ha,hlow,hpow,hcost⟩ :=
    BB6.Agent13LowFanPower.all_low_ray_parents_are_even_bounce
      z u a k hu hedge
  have haodd : a%2=1 := by
    have hp : 2^n*(2*(a-1)+8)=346*u+54 := hpow.symm
    have hh : a-1=2*((a-1)/2) := by omega
    omega
  have hfactor : 2*(a-1)+8=4*((a-1)/2+2) := by omega
  have hval : 2^(n+2)∣346*u+54 := by
    refine ⟨(a-1)/2+2,?_⟩
    calc
      346*u+54=2^n*(2*(a-1)+8) := hpow
      _=2^n*(4*((a-1)/2+2)) := by rw [hfactor]
      _=2^(n+2)*((a-1)/2+2) := by
        rw [Nat.pow_add]
        simp only [show (2:Nat)^2=4 by decide]
        ac_rfl
  have hdiv : 2^n∣519*z+73 :=
    (BB6.Agent13LowFanDivisor.low_mass_divisor_iff z u n hu).mp hval
  have hodd : (519*z+73)%2=1 := by omega
  have hn0 : n=0 := by
    by_contra hh
    have hge : 1≤n := by omega
    have hd : 2∣(2:Nat)^n := by
      have h := Nat.pow_dvd_pow 2 hge
      simpa only [show (2:Nat)^1=2 by decide] using h
    have hd2 : 2∣519*z+73 := dvd_trans hd hdiv
    have he : (519*z+73)%2=0 := Nat.mod_eq_zero_of_dvd hd2
    omega
  subst n
  simp at hpow hcost
  have haeq : a=173*u+24 := by omega
  have hkeq : k=(339*u+47)/2 := by omega
  rw [haeq,hkeq] at hpre
  exact hpre

#print axioms even_low_ray_reach_forces_unique_parent
end BB6.Agent13LowEvenRoot
