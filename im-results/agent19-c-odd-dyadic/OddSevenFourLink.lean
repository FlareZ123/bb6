import OddSevenForcedRoot
import EvenRightSixOrbit
import ReachAffine
import Agent3COrbitIff
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19Four
open BB6.Agent46

/-- For all u and v>=2, this entire two-dimensional original-source
    Machine C blank-root sector is impossible. The first backward edge
    is in the genuinely branching sum-seven sector, but its second
    parent is excluded using the actual blank-root odd-image theorem.
    Three subsequent affine source edges reach a forbidden odd image. -/
theorem blank_no_four_link_slope (u v : Nat) (hv : 2≤v) :
    ¬ BB6.Agent3.CReach (32*u+1) (64*v+14) := by
  intro h
  have h1 : BB6.Agent3.CReach (32*u+64*v+13) (32*v+6) := by
    have ht := (BB6.Agent19Seven.sumseven_forced_root_iff
      (32*u+1) (64*v+14) (by omega) (by omega) (by omega) (by omega)).mp h
    have ha : (32*u+1)+(64*v+14)-2=32*u+64*v+13 := by omega
    have hk : ((64*v+14)-2)/2=32*v+6 := by omega
    rw [ha,hk] at ht
    exact ht
  have h2 : BB6.Agent3.CReach (32*u+96*v+17) (16*v+2) := by
    have ht := (six_even_right_blank_reach_iff
      (32*u+64*v+13) (32*v+6)
      (by omega) (by omega) (by omega) (by omega)).mp h1
    have ha : (32*u+64*v+13)+(32*v+6)-2=32*u+96*v+17 := by omega
    have hk : ((32*v+6)-2)/2=16*v+2 := by omega
    rw [ha,hk] at ht
    exact ht
  have h3 : BB6.Agent3.CReach (32*u+112*v+17) (8*v) := by
    have ht := (six_even_right_blank_reach_iff
      (32*u+96*v+17) (16*v+2)
      (by omega) (by omega) (by omega) (by omega)).mp h2
    have ha : (32*u+96*v+17)+(16*v+2)-2=32*u+112*v+17 := by omega
    have hk : ((16*v+2)-2)/2=8*v := by omega
    rw [ha,hk] at ht
    exact ht
  have h4 : BB6.Agent3.CReach (32*u+120*v+15) (4*v-1) := by
    have ht := (BB6.Agent15.blank_reach_iff_affine
      (32*u+112*v+17) (8*v)
      (by omega) (by omega) (by omega)).mp h3
    have ha : (32*u+112*v+17)+(8*v)-2=32*u+120*v+15 := by omega
    have hk : ((8*v)-2)/2=4*v-1 := by omega
    rw [ha,hk] at ht
    exact ht
  rcases h4 with ⟨time,hr⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at hr
  | succ t =>
      have hi := BB6.Agent3.blank_section_odd_image t
        (32*u+120*v+15) (4*v-1) hr (by omega) (by omega)
      omega

#print axioms blank_no_four_link_slope
end BB6.Agent19Four
