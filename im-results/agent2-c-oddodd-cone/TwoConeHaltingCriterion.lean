import OddOddHighIntegration
import ThirdImageConeSource
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0

namespace BB6.Agent2CTwoConeCriterion

/-- Strongest inherited both-branch six-sector source criterion, further
    restricted by two new, disjoint original-source proven high-stop
    congruence families. Both are universally quantified over all m,j. -/
def highAllowed (j m : Nat) : Prop :=
  BB6.Agent2COddOddIntegration.highAllowed j m ∧
    ¬ (m%64=6 ∧ j%256=(3*m+38)%256)

private theorem high_bound (j m : Nat) :
    j+3*m+5≤2^(2*m+2)*(j+3) := by
  have hp : 4*m+4 ≤ 2^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hpow : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hpow
  rw [Nat.mul_add]
  omega

/-- A lossless strengthening of the source-authenticated Machine C
    original-blank halting iff. The new outer high condition eliminates
    both the 48/64 two-return missing cone and the strict I2-not-I3
    cylinder; no upper index cutoff or time bound is assumed. -/
theorem blank_halts_iff_two_cones :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11SixAll.lowAllowed m ∧
        BB6.Agent11SixForced.sixForcedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
        BB6.Agent11SixForced.sixForcedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent2COddOddIntegration.blank_halts_iff_six_oddodd]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
      have hn : ¬(m%64=6 ∧ j%256=(3*m+38)%256) := by
        rintro ⟨hm,hj⟩
        have hr : BB6.Agent3.CReach (2*j+3) k :=
          (BB6.Agent11SixForced.sixForcedRootDecision_iff (2*j+3) k).mp hroot
        have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
          dsimp [k]
          have hc := Nat.sub_add_cancel (high_bound j m)
          omega
        rcases hr with ⟨time,ht⟩
        exact (BB6.Agent2CThirdImage.high_stop_blank_unreachable
          j m k time hm hj hstop) ht
      exact Or.inr ⟨j,m,⟨hprior,hn⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

#print axioms blank_halts_iff_two_cones

end BB6.Agent2CTwoConeCriterion
