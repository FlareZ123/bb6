import CThreeSixM32Integration
import LowM67SeventeenCriterion
import Lean.Elab.Tactic.Omega

namespace BB6.Agent13Joint65M32

/-- Strongest combined source-connected exact blank-halting criterion here:
    65/512 all-time original-source low-stop parameter exclusions,
    together with the M32 high-pair source-embedded quotient obstruction.
    Neither existential is bounded or decided. -/
def lowAllowed (m : Nat) : Prop :=
  BB6.Agent13Low17Joint.lowAllowedSource17 m

def highAllowed (j m : Nat) : Prop :=
  BB6.Agent13M32Integration.highAllowedM32 j m

private theorem high_bound (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hp : 4*m+4 ≤ 2^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hpow : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hpow
  rw [Nat.mul_add]
  omega

theorem blank_halts_iff_low65_m32 :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowed m ∧
        BB6.Agent11SixForced.sixForcedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
        BB6.Agent11SixForced.sixForcedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent13Low17Joint.blank_halts_iff_six_low17]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
      have hr : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent11SixForced.sixForcedRootDecision_iff (2*j+3) k).mp hroot
      have hnot : (3≤j ∧ 2≤m) →
          ¬ CCert.highPairGood (j%32) (m%32) := by
        intro hbounds hgood
        rcases hbounds with ⟨hj,hm⟩
        have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
          dsimp [k]
          have hc := Nat.sub_add_cancel (high_bound j m)
          omega
        have hr15 : BB6.Agent15.CReach (2*j+3) k := by
          simpa [BB6.Agent3.CReach, BB6.Agent15.CReach] using hr
        have hline : BB6CLine.Reach (2*j+3,k,0) :=
          BB6.Agent15.m32_section_reach_embeds hr15
        exact (BB6.Agent4M32.high32_forbidden_source
          j m k hj hm hstop hgood) hline
      exact Or.inr ⟨j,m,⟨hprior,hnot⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

#print axioms blank_halts_iff_low65_m32
end BB6.Agent13Joint65M32
