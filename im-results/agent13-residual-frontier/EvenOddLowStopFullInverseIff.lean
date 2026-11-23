import EvenOddLowStopDivisor
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace BB6.Agent13LowFullInverse
open BB6.Agent46

/-- The COMPLETE ORIGINAL-SOURCE immediate predecessor relation for
    every necessary low-stop ray R_u, all unbounded z and all bounce
    depths n. This is a genuine iff: arithmetic sufficient conditions
    construct a literal original-machine section edge, not merely an
    inverse-quotient candidate. The exceptional a=0,1, direct and
    even-source branches have all been eliminated using the proved
    non-power dyadic gap and exact full source grammar. -/
theorem low_stop_section_parent_iff
    (z u a k : Nat)
    (hu : u+6*z+1=2^(1024*z+129)) :
    secNext (a,k)=some (180*u+28,166*u+25) ↔
    ∃ n : Nat, n%2=0 ∧ 3≤a ∧ a<2*k ∧
      346*u+54=2^(n+1)*(a+3) ∧
      2*k+a+7+3*n=512*u+78 := by
  constructor
  · intro hedge
    obtain ⟨n,hn,ha,hlow,hpow,hcost⟩ :=
      BB6.Agent13LowFanPower.all_low_ray_parents_are_even_bounce
        z u a k hu hedge
    have hfactor : 2*(a-1)+8=2*(a+3) := by omega
    have hmass : 346*u+54=2^(n+1)*(a+3) := by
      calc
        346*u+54=2^n*(2*(a-1)+8) := hpow
        _=2^n*(2*(a+3)) := by rw [hfactor]
        _=2^(n+1)*(a+3) := by rw [Nat.pow_succ]; ac_rfl
    have hcost' : 2*k+a+7+3*n=512*u+78 := by omega
    exact ⟨n,hn,ha,hlow,hmass,hcost'⟩
  · rintro ⟨n,hn,ha,hlow,hmass,hcost⟩
    have hao : a%2=1 := by omega
    have hne0 : a≠0 := by omega
    have hne1 : a≠1 := by omega
    have hk0 : k≠0 := by omega
    have hhigh : ¬ 2*k≤a := by omega
    have hae : ¬ a%2=0 := by omega
    have hbase : 2*(a-1)+8=2*(a+3) := by omega
    have hpow : 180*u+28+166*u+25+1=2^n*(2*(a-1)+8) := by
      calc
        180*u+28+166*u+25+1=346*u+54 := by omega
        _=2^(n+1)*(a+3) := hmass
        _=2^n*(2*(a-1)+8) := by
          rw [hbase,Nat.pow_succ]
          ac_rfl
    have hcost' :
        (2*k-a+3)+(2*(a-1)+8)+3*n =
          (180*u+28)+2*(166*u+25)+2 := by omega
    have hp : sectionPreimageCriterion a k (180*u+28) (166*u+25) := by
      simp only [sectionPreimageCriterion,
        if_neg hne0,if_neg hne1,if_neg hk0,
        if_neg hhigh,if_neg hae]
      exact ⟨n,hpow,hcost'⟩
    exact (complete_section_inverse a k _ _ (by omega)).mpr hp

#print axioms low_stop_section_parent_iff
end BB6.Agent13LowFullInverse
