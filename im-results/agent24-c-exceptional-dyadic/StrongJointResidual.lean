import PhaseResidual
import ValSixC58AllDepth
import Lean.Elab.Tactic.Omega

namespace BB6.Agent24Phase

/-- Merge the complete, source-certified C58/ValSix high predicate,
    the previously established odd-dyadic all-depth sieve, and both
    new even-right exceptional-phase all-depth classes. -/
def highAllowed (j m : Nat) : Prop :=
    BB6.Agent11C58AllDepth.highAllowed j m ∧
    ¬ BB6.Agent46.allPhaseExcluded j m

private theorem high_score_nonnegative (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hm : 4*m+4 ≤ 2^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hp : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  rw [Nat.mul_add]
  omega

/-- Source-exact integrated Machine C blank halting iff with the entire
    prior C58/ValSix and Agent19 all-depth sieve, plus our two novel
    all-phase inverse classes. The remaining existential is unbounded. -/
theorem blank_halts_iff_c58_two_sided_all_phase :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11C58ValSix.lowAllowed m ∧
         BB6.Agent3ValSix.valSixMixedRootDecision 1
           (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
         BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
           (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent11C58AllDepth.blank_halts_iff_joint_c58_all_depth]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
      have hr : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff _ _).mp hroot
      have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
        dsimp [k]
        have hc := Nat.sub_add_cancel (high_score_nonnegative j m)
        omega
      have hnot : ¬ BB6.Agent46.allPhaseExcluded j m := by
        rintro ⟨r,hr8,hwidth,hbranch⟩
        rcases hbranch with ⟨hj,hpair⟩ | ⟨hj,hpair⟩
        · exact BB6.Agent46.high_all_phase_A_no_blank r j m k
             hr8 hwidth hj hpair hstop hr
        · exact BB6.Agent46.high_all_phase_B_no_blank r j m k
             hr8 hwidth hj hpair hstop hr
      exact Or.inr ⟨j,m,⟨hprior,hnot⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

#print axioms blank_halts_iff_c58_two_sided_all_phase
end BB6.Agent24Phase
