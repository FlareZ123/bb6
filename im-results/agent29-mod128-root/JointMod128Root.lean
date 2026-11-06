import JointAllRoot
import RootMod128HighSource
import RootMod128ThreeHigh
import RootMod128FourHigh
import RootMod128AfterSevenHigh
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29Joint

/-- Merge the four separate new genuine-blank high-stopping exclusions
into the strongest currently available Agent19 true-root criterion. -/
def highAllowedPlus (j m : Nat) : Prop :=
  BB6.Agent19Joint.highAllowed j m ∧
  ¬(4≤m ∧ j%8=5 ∧ (j+31)%128=(3*m)%128) ∧
  ¬(4≤m ∧ j%32=17 ∧ (j+31)%128=(3*m)%128) ∧
  ¬(4≤m ∧ j%64=57 ∧ (j+31)%128=(3*m)%128) ∧
  ¬(m%32=6 ∧ (j+51)%256=(9*m)%256)

private theorem high_score_nonnegative (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hm : 4*m+4 ≤ 2^(2*m+2) := BB6.Agent29New.power_linear_bound m
  have hp : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  have hd : 2^(2*m+2)*(j+3) =
      2^(2*m+2)*j+3*2^(2*m+2) := by
    simp [Nat.mul_add, Nat.mul_comm]
  omega

/-- Time-free, source-exact joint blank halting iff, retaining all
established prior restrictions and the four new infinite high exclusions.
The infinite existentials remain unknown. -/
theorem blank_halts_iff_joint_mod128 :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent3.jointLowAllowed m ∧
        BB6.Agent3.mixedFastRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedPlus j m ∧
        BB6.Agent3.mixedFastRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent19Joint.blank_halts_iff_combined_parametric]
  constructor
  · rintro (hlow | ⟨j,m,hallowed,hroot⟩)
    · exact Or.inl hlow
    · let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
      have hr : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent3.mixedFastRootDecision_iff (2*j+3) k).mp hroot
      have hgate : k+j+3*m+5=2^(2*m+2)*(j+3) := by
        dsimp [k]
        have hc := Nat.sub_add_cancel (high_score_nonnegative j m)
        omega
      have h1 : ¬(4≤m ∧ j%8=5 ∧ (j+31)%128=(3*m)%128) := by
        rintro ⟨hm,hj,hs⟩
        exact BB6.Agent29New.blank_no_high_stop_mod128 j m k hm hj hs hgate hr
      have h2 : ¬(4≤m ∧ j%32=17 ∧ (j+31)%128=(3*m)%128) := by
        rintro ⟨hm,hj,hs⟩
        exact BB6.Agent29New.blank_no_high_stop_three j m k hm hj hs hgate hr
      have h3 : ¬(4≤m ∧ j%64=57 ∧ (j+31)%128=(3*m)%128) := by
        rintro ⟨hm,hj,hs⟩
        exact BB6.Agent29New.blank_no_high_stop_four j m k hm hj hs hgate hr
      have h4 : ¬(m%32=6 ∧ (j+51)%256=(9*m)%256) := by
        rintro ⟨hm,hj⟩
        exact BB6.Agent29New.blank_no_high_after_seven j m k hm hj hgate hr
      exact Or.inr ⟨j,m,⟨hallowed,h1,h2,h3,h4⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hallowed,_,_,_,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hallowed,hroot⟩

#print axioms blank_halts_iff_joint_mod128
end BB6.Agent29Joint
