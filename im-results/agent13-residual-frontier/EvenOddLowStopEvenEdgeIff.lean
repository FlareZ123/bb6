import EvenOddLowStopFullInverseIff
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace BB6.Agent13LowEvenEdge

/-- Exact classification of the *entire original-source section fiber*
    over the authentic low-stop target R_u when z is even. Every genuine
    edge into R_u has precisely this explicit parent, and the displayed
    parent always has a genuine edge into R_u. In particular the actual
    source indegree of every such R_u is EXACTLY ONE, for all unbounded
    even z. No blank reachability or halting is assumed. -/
theorem even_low_ray_source_parent_iff
    (z u a k : Nat)
    (hu : u+6*z+1=2^(1024*z+129))
    (hz : z%2=0) :
    BB6.Agent46.secNext (a,k)=some (180*u+28,166*u+25) ↔
      a=173*u+24 ∧ k=(339*u+47)/2 := by
  have hpow4 : 4 ∣ (2:Nat)^(1024*z+129) := by
    have hh : (2:Nat)^2 ∣ 2^(1024*z+129) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^2=4 by decide] using hh
  have hpowmod : (2^(1024*z+129))%4=0 :=
    Nat.mod_eq_zero_of_dvd hpow4
  have humod : u%4=3 := by omega
  have hQmod : (346*u+54)%8=4 := by omega
  have huodd : u%2=1 := by omega
  have hkmod : (339*u+47)%2=0 := by omega
  have hktwice : 2*((339*u+47)/2)=339*u+47 := by
    have hh := Nat.mod_add_div (339*u+47) 2
    omega
  constructor
  · intro hedge
    obtain ⟨n,hn,ha,hlow,hmass,hcost⟩ :=
      (BB6.Agent13LowFullInverse.low_stop_section_parent_iff
        z u a k hu).mp hedge
    have hn0 : n=0 := by
      by_cases hzero : n=0
      · exact hzero
      · have hnge : 2≤n := by omega
        have hdiv8power : 8 ∣ (2:Nat)^(n+1) := by
          have hh : (2:Nat)^3∣2^(n+1) :=
            Nat.pow_dvd_pow 2 (by omega)
          simpa only [show (2:Nat)^3=8 by decide] using hh
        rcases hdiv8power with ⟨v,hv⟩
        have hdiv8 : 8∣346*u+54 := by
          refine ⟨v*(a+3),?_⟩
          calc
            346*u+54=2^(n+1)*(a+3) := hmass
            _=(8*v)*(a+3) := by rw [hv]
            _=8*(v*(a+3)) := by ac_rfl
        have hh : (346*u+54)%8=0 := Nat.mod_eq_zero_of_dvd hdiv8
        omega
    subst n
    simp at hmass hcost
    constructor <;> omega
  · rintro ⟨ha,hk⟩
    subst a
    subst k
    apply (BB6.Agent13LowFullInverse.low_stop_section_parent_iff
      z u (173*u+24) ((339*u+47)/2) hu).mpr
    refine ⟨0,by decide,by omega,by omega,?_,?_⟩
    · simp only [show 0+1=1 by decide,show (2:Nat)^1=2 by decide]
      omega
    · simp only [show (3:Nat)*0=0 by decide]
      omega

#print axioms even_low_ray_source_parent_iff
end BB6.Agent13LowEvenEdge
