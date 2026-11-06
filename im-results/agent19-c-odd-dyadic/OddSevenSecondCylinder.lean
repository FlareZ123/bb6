import OddSevenSecondRoot
import ReachAffine
import Agent3COrbitIff
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19Second
open BB6.Agent46

/-- An original-source, infinite two-parameter two-link forbidden
    cylinder across the second dyadic sum-seven inverse branch. The
    source bounce competitor has already been ruled out in the first
    root theorem; the direct source branch leads to a forbidden
    odd-image state after one further source-exact inverse edge. -/
theorem blank_no_second_slope (u v : Nat)
    (hv : 2≤v) (hres : (5*u+v)%8=2) :
    ¬ BB6.Agent3.CReach (16*u+13) (16*v+2) := by
  intro hr
  have hmod : ((16*u+13)+(16*v+2)+1)%32=16 := by omega
  have hcyl : (5*(16*u+13)+9*(16*v+2))%128=115 := by omega
  have hroot := (second_sumseven_forced_root_iff
    (16*u+13) (16*v+2) (by omega) (by omega) (by omega)
    hmod hcyl (by omega)).mp hr
  have h1 : BB6.Agent3.CReach (16*u+16*v+13) (8*v) := by
    have ha : (16*u+13)+(16*v+2)-2=16*u+16*v+13 := by omega
    have hk : ((16*v+2)-2)/2=8*v := by omega
    rw [ha,hk] at hroot
    exact hroot
  have h2 : BB6.Agent3.CReach (16*u+24*v+11) (4*v-1) := by
    have hh := (BB6.Agent15.blank_reach_iff_affine
      (16*u+16*v+13) (8*v) (by omega) (by omega) (by omega)).mp h1
    have ha : (16*u+16*v+13)+(8*v)-2=16*u+24*v+11 := by omega
    have hk : ((8*v)-2)/2=4*v-1 := by omega
    rw [ha,hk] at hh
    exact hh
  rcases h2 with ⟨n,hn⟩
  cases n with
  | zero =>
      simp [BB6.Agent8Section.run] at hn
  | succ n =>
      have hi := BB6.Agent3.blank_section_odd_image n
        (16*u+24*v+11) (4*v-1) hn (by omega) (by omega)
      omega

#print axioms blank_no_second_slope
end BB6.Agent19Second
