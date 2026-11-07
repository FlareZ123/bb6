import ValSixC58
import HighDyadicLowVal
import HighDyadicPrior
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11C58Dyadic

/-- The strongest existing Agent3/11/19/29 ValSixFull+C58 predicate,
    retaining every earlier restriction while deleting a source-exact
    infinite high-dyadic stopping family. -/
def highAllowed (j m : Nat) : Prop :=
  BB6.Agent11C58ValSix.highAllowed j m ∧
  ¬(3≤m ∧ m%4=3 ∧ (j+9*m+14)%64=48)

/-- The exact authentic Machine C blank-halting criterion after combining
    the full ValSix+C58 source chain with the novel high-dyadic exclusion.
    The unrestricted low/high parameter existentials are still open. -/
theorem blank_halts_iff_joint_c58_dyadic :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11C58ValSix.lowAllowed m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent11C58ValSix.blank_halts_iff_joint_val_six_c58]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · have hreach : BB6.Agent3.CReach (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5)) :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff _ _).mp hroot
      have hnew : ¬(3≤m ∧ m%4=3 ∧ (j+9*m+14)%64=48) := by
        rintro ⟨hm3,hm4,hpair⟩
        exact (BB6.Agent19HighDyadic.high_dyadic_stopping_target_unreachable
          j m hm3 hm4 hpair) hreach
      exact Or.inr ⟨j,m,⟨hprior,hnew⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

/-- All previous ValSixFull+C58 restrictions admit this infinite family,
    yet the new source-exact high dyadic criterion rejects every member. -/
theorem new_high_dyadic_independent (r : Nat) :
    BB6.Agent11C58ValSix.highAllowed (7+64*r) 3 ∧
    ¬ highAllowed (7+64*r) 3 := by
  refine ⟨BB6.Agent11C58ValSix.previous_combined_admits_high_dyadic r,?_⟩
  intro h
  exact h.2 ⟨by omega,by omega,by omega⟩

#print axioms blank_halts_iff_joint_c58_dyadic
#print axioms new_high_dyadic_independent
end BB6.Agent11C58Dyadic
