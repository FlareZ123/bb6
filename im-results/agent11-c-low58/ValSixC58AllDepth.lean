import ValSixC58
import HighDyadicAllDepth
import HighDyadicPrior
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11C58AllDepth

/-- All previous source-certified restrictions together with every
    dyadic-depth high stopping exclusion. The universal quantifier
    is bounded by r+4<=2*m+2 whenever its body applies. -/
def highAllowed (j m : Nat) : Prop :=
  BB6.Agent11C58ValSix.highAllowed j m ∧
  ∀ r : Nat, ¬(2≤r ∧ 3≤m ∧ r+4≤2*m+2 ∧
    m%4=(2*r+3)%4 ∧
    (j+9*m+14)%2^(r+4)=3*2^(r+2))

/-- Exact source-authentic blank halting equivalence after removing
    all compatible dyadic inverse-depth high cylinders. Neither
    existential parameter branch has a proven finite global bound. -/
theorem blank_halts_iff_joint_c58_all_depth :
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
      have hall : ∀ r : Nat, ¬(2≤r ∧ 3≤m ∧ r+4≤2*m+2 ∧
          m%4=(2*r+3)%4 ∧
          (j+9*m+14)%2^(r+4)=3*2^(r+2)) := by
        intro r
        rintro ⟨hr,hm,hdepth,hm4,hpair⟩
        exact (BB6.Agent19AllDepth.high_depth_stopping_target_no_blank
          r j m hr hm hdepth hm4 hpair) hreach
      exact Or.inr ⟨j,m,⟨hprior,hall⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

/-- Disjoint old-sieve-admitted infinite families are separately
    eliminated at depth 2 (m=3) and depth 3 (m=5). -/
theorem all_depth_two_independent (t : Nat) :
    BB6.Agent11C58ValSix.highAllowed (7+64*t) 3 ∧
    ¬ highAllowed (7+64*t) 3 := by
  refine ⟨BB6.Agent11C58ValSix.previous_combined_admits_high_dyadic t,?_⟩
  intro h
  exact h.2 2 ⟨by omega,by omega,by omega,by omega,by omega⟩

theorem all_depth_three_independent (t : Nat) :
    BB6.Agent11C58ValSix.highAllowed (37+128*t) 5 ∧
    ¬ highAllowed (37+128*t) 5 := by
  refine ⟨BB6.Agent11C58ValSix.previous_combined_admits_high_depth_three t,?_⟩
  intro h
  exact h.2 3 ⟨by omega,by omega,by omega,by omega,by omega⟩

#print axioms blank_halts_iff_joint_c58_all_depth
#print axioms all_depth_two_independent
#print axioms all_depth_three_independent
end BB6.Agent11C58AllDepth
