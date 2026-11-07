import ValSixC58
import HighDyadicAllDepth
import HighDyadicPrior
import HighDyadicAllDepthPrior
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

/-- An infinite, depth-unbounded subfamily survives the old combined
    ValSixFull+C58 sieve but is eliminated by the new exact source cone. -/
theorem infinite_depth_old_sieve_independence (t : Nat) :
    BB6.Agent11C58ValSix.highAllowed
      (BB6.Agent19AllDepth.depthJ (130+128*t))
      (BB6.Agent19AllDepth.depthM (130+128*t)) ∧
    ¬ highAllowed
      (BB6.Agent19AllDepth.depthJ (130+128*t))
      (BB6.Agent19AllDepth.depthM (130+128*t)) := by
  let r := 130+128*t
  let j := BB6.Agent19AllDepth.depthJ r
  let m := BB6.Agent19AllDepth.depthM r
  have hr : 2≤r := by dsimp [r]; omega
  obtain ⟨hm,hd,hm4,hpair⟩ :=
    BB6.Agent19AllDepth.depth_family_parameters r hr
  refine ⟨BB6.Agent11C58AllDepthPrior.distinct_depth_family_survives_old t,?_⟩
  intro h
  exact h.2 r ⟨hr,hm,hd,hm4,hpair⟩

/-- Different depth indices in that progression have distinct high m,
    providing genuinely infinitely many previously admitted exclusions. -/
theorem infinite_depth_indices_distinct (s t : Nat)
    (he : BB6.Agent19AllDepth.depthM (130+128*s) =
      BB6.Agent19AllDepth.depthM (130+128*t)) : s=t := by
  have hdepth := BB6.Agent19AllDepth.depthM_injective_on_two
    (130+128*s) (130+128*t) (by omega) (by omega) he
  omega

#print axioms infinite_depth_old_sieve_independence
#print axioms infinite_depth_indices_distinct
#print axioms blank_halts_iff_joint_c58_all_depth
#print axioms all_depth_two_independent
#print axioms all_depth_three_independent
end BB6.Agent11C58AllDepth
