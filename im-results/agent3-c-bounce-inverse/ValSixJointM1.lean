import ValSixJointFast
import SecondOneInfinite
import JointM1PriorAllowed
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3ValSix

/-- Closed form for Agent29's second-family m=1 stopping-index tower:
    5*j_r+14 = 64*16^r. -/
theorem second_one_indices_closed_form (r : Nat) :
    5 * BB6.Agent29Depth.secondOneJ r + 14 = 64 * 16^r := by
  induction r with
  | zero => decide
  | succ r ih =>
      rw [Nat.pow_succ]
      change 5 * (16 * BB6.Agent29Depth.secondOneJ r + 42) + 14 =
        64 * (16^r * 16)
      omega

/-- The excluded m=1 indices are strictly increasing, hence infinite. -/
theorem second_one_indices_strict (r : Nat) :
    BB6.Agent29Depth.secondOneJ r <
      BB6.Agent29Depth.secondOneJ (r+1) := by
  change BB6.Agent29Depth.secondOneJ r <
    16 * BB6.Agent29Depth.secondOneJ r + 42
  omega

/-- Every index in the m=1 right-four tower was admitted by the
    strongest previously source-certified Agent19/29/3 high sieve. -/
theorem second_one_family_previously_allowed (r : Nat) :
    highAllowedValSixThree (BB6.Agent29Depth.secondOneJ r) 1 := by
  have hprior : BB6.Agent19Joint.highAllowed
      (BB6.Agent29Depth.secondOneJ r) 1 :=
    BB6.Agent29Prior.all_j_mod32_ten_prior_allowed _
      (BB6.Agent29Depth.secondOneJ_mod32 r)
  have hplus : BB6.Agent29Joint.highAllowedPlus
      (BB6.Agent29Depth.secondOneJ r) 1 := by
    unfold BB6.Agent29Joint.highAllowedPlus
    exact ⟨hprior, by omega, by omega, by omega, by omega⟩
  unfold highAllowedValSixThree highAllowedValSix
  exact ⟨⟨hplus, by omega, by omega⟩, by omega⟩

/-- The stronger high-parameter predicate removes the infinite m=1
    right-four tower while retaining every other previously admitted
    high parameter. -/
def highAllowedValSixM1 (j m : Nat) : Prop :=
  highAllowedValSixThree j m ∧
  ¬ (m=1 ∧ ∃ r, j=BB6.Agent29Depth.secondOneJ r)

/-- Exact original blank-start Machine C halting iff with Agent29's
    source-certified infinite m=1 right-four tower removed from the
    parameter set. The remaining low/high parameter existentials are
    still unbounded. -/
theorem blank_halts_iff_joint_val_six_m1 :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent3.jointLowAllowed m ∧
        valSixMixedRootDecision 1 (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedValSixM1 j m ∧
        valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [blank_halts_iff_joint_val_six_fast]
  constructor
  · rintro (hlow | ⟨j,m,hallowed,hroot⟩)
    · exact Or.inl hlow
    · have hnew : ¬ (m=1 ∧ ∃ r, j=BB6.Agent29Depth.secondOneJ r) := by
        intro h
        rcases h with ⟨hm,r,hj⟩
        subst m
        subst j
        have hstop := BB6.Agent29Depth.second_one_family_stopping r
        have hpow : (2:Nat)^(2*1+2)=16 := by decide
        have hk :
            (2:Nat)^(2*1+2)*
              (BB6.Agent29Depth.secondOneJ r+3) -
              (BB6.Agent29Depth.secondOneJ r+3*1+5) =
            15*BB6.Agent29Depth.secondOneJ r+40 := by
          rw [hpow] at hstop ⊢
          omega
        have hroot' :
            valSixMixedRootDecision
              (2*BB6.Agent29Depth.secondOneJ r+3)
              (15*BB6.Agent29Depth.secondOneJ r+40)=true := by
          simpa [hk] using hroot
        have hreach : BB6.Agent15.CReach
            (2*BB6.Agent29Depth.secondOneJ r+3)
            (15*BB6.Agent29Depth.secondOneJ r+40) :=
          (valSixMixedRootDecision_iff _ _).mp hroot'
        exact BB6.Agent29Depth.second_one_family_unreachable r hreach
      exact Or.inr ⟨j,m,⟨hallowed,hnew⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hallowed,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hallowed,hroot⟩

#print axioms second_one_indices_closed_form
#print axioms second_one_indices_strict
#print axioms second_one_family_previously_allowed
#print axioms blank_halts_iff_joint_val_six_m1

end BB6.Agent3ValSix
