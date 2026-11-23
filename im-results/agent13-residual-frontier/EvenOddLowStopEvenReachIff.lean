import EvenOddLowStopEvenUnique
import EvenOddLowStopFullInverseIff
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace BB6.Agent13LowEvenIff
open BB6.Agent46

/-- For every even low-stop ray index z, the genuine original Machine C
    section blank-reachability of R_u is EXACTLY equivalent to that of
    its single available true predecessor (173u+24, (339u+47)/2).
    No finite depth, time or z bound. The converse uses the exact
    source section transition, not just necessary inverse arithmetic. -/
theorem even_low_ray_reach_iff_unique_parent
    (z u : Nat)
    (hu : u+6*z+1=2^(1024*z+129))
    (hz : z%2=0) :
    BB6.Agent3.CReach (180*u+28) (166*u+25) ↔
    BB6.Agent3.CReach (173*u+24) ((339*u+47)/2) := by
  constructor
  · exact BB6.Agent13LowEvenRoot.even_low_ray_reach_forces_unique_parent
      z u hu hz
  · intro hr
    have hpow2 : 2 ∣ (2:Nat)^(1024*z+129) := by
      have hp : (2:Nat)^1 ∣ 2^(1024*z+129) :=
        Nat.pow_dvd_pow 2 (by omega)
      simpa only [show (2:Nat)^1=2 by decide] using hp
    have hpmod : (2^(1024*z+129))%2=0 :=
      Nat.mod_eq_zero_of_dvd hpow2
    have huodd : u%2=1 := by omega
    have hkm : (339*u+47)%2=0 := by omega
    have hktwice : 2*((339*u+47)/2)=339*u+47 := by
      have hh := Nat.mod_add_div (339*u+47) 2
      omega
    have hedge : secNext ((173*u+24),((339*u+47)/2))=
        some (180*u+28,166*u+25) := by
      apply (BB6.Agent13LowFullInverse.low_stop_section_parent_iff
        z u (173*u+24) ((339*u+47)/2) hu).mpr
      refine ⟨0,by decide,by omega,by omega,?_,?_⟩
      · norm_num
        omega
      · norm_num
        omega
    rcases hr with ⟨time,ht⟩
    refine ⟨time+1,?_⟩
    simpa [BB6.Agent8Section.run,ht] using hedge

#print axioms even_low_ray_reach_iff_unique_parent
end BB6.Agent13LowEvenIff
