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
  have hp4 : 4 ∣ (2:Nat)^(1024*z+129) := by
    have hd : (2:Nat)^2 ∣ 2^(1024*z+129) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^2=4 by decide] using hd
  have hpmod : (2^(1024*z+129))%4=0 :=
    Nat.mod_eq_zero_of_dvd hp4
  have humod : u%4=3 := by omega
  have hQmod : (346*u+54)%8=4 := by omega
  have hn0 : n=0 := by
    by_cases hzero : n=0
    · exact hzero
    · have hnge : 2≤n := by omega
      have hdiv4 : 4 ∣ (2:Nat)^n := by
        have hd : (2:Nat)^2∣2^n := Nat.pow_dvd_pow 2 hnge
        simpa only [show (2:Nat)^2=4 by decide] using hd
      rcases hdiv4 with ⟨v,hv⟩
      have hfactor : 2*(a-1)+8=2*(a+3) := by omega
      have hdiv8 : 8 ∣ 346*u+54 := by
        refine ⟨v*(a+3),?_⟩
        calc
          346*u+54=2^n*(2*(a-1)+8) := hpow
          _=(4*v)*(2*(a+3)) := by rw [hv,hfactor]
          _=(4*2)*(v*(a+3)) := by ac_rfl
          _=8*(v*(a+3)) := by rfl
      have hh : (346*u+54)%8=0 := Nat.mod_eq_zero_of_dvd hdiv8
      omega
  subst n
  simp at hpow hcost
  have haeq : a=173*u+24 := by omega
  have hkeq : k=(339*u+47)/2 := by omega
  rw [haeq,hkeq] at hpre
  exact hpre

#print axioms even_low_ray_reach_forces_unique_parent
end BB6.Agent13LowEvenRoot
