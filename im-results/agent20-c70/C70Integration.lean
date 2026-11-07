import C70Rectangle
import StrongJointResidual
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20C70

/-- All of this infinite low parameter class survived the previously
    strongest integrated source sieve; its elimination is strictly new
    relative to that exact Boolean residual. -/
theorem prior_low_admits_18 (t : Nat) :
    BB6.Agent11C58ValSix.lowAllowed (128*t+18) := by
  unfold BB6.Agent11C58ValSix.lowAllowed
    BB6.Agent3ValSix.lowAllowedValSixFull
    BB6.Agent11Joint.lowAllowed
    BB6.Agent3.jointLowAllowed
  omega

def lowAllowedC70 (m : Nat) : Prop :=
  BB6.Agent11C58ValSix.lowAllowed m ∧ m%128 ≠18

private theorem low_bound_C70 (m : Nat) :
    3*m+4 ≤ 2^(2*m+3) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+3=(2*m+3)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

/-- Source-exact Machine C blank halting iff after appending the
    entire new low cylinder to the previous joint C58/ValSix + all-phase
    high sieve, preserving the exact fixed-target reachability oracle. -/
theorem blank_halts_iff_c70 :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowedC70 m ∧
         BB6.Agent3ValSix.valSixMixedRootDecision 1
           (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, BB6.Agent24Phase.highAllowed j m ∧
         BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
           (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent24Phase.blank_halts_iff_c58_two_sided_all_phase]
  constructor
  · rintro (⟨m,hprior,hroot⟩ | ⟨j,m,hprior,hroot⟩)
    · let k := 2^(2*m+3)-(3*m+4)
      have hr : BB6.Agent3.CReach 1 k :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff 1 k).mp hroot
      have hnon : m%128 ≠18 := by
        intro hm
        have hstop : k+3*m+4=2^(2*m+3) := by
          dsimp [k]
          have hc := Nat.sub_add_cancel (low_bound_C70 m)
          omega
        exact (blank_no_low_depth_18_mod128 m k hm hstop) hr
      exact Or.inl ⟨m,⟨hprior,hnon⟩,hroot⟩
    · exact Or.inr ⟨j,m,hprior,hroot⟩
  · rintro (⟨m,⟨hprior,_⟩,hroot⟩ | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl ⟨m,hprior,hroot⟩
    · exact Or.inr ⟨j,m,hprior,hroot⟩

/-- The exact high stopping sieve additionally removes two new
    parameter rectangles, uniformly at every right depth. -/
def highAllowedC70 (j m : Nat) : Prop :=
  BB6.Agent24Phase.highAllowed j m ∧
  ¬((j%128=63 ∧ m%128=82) ∨ (j%128=127 ∧ m%128=18))

private theorem high_bound_C70 (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hm : 4*m+4 ≤ 2^(2*m+2) := by
    induction m with
    | zero => decide
    | succ m ih =>
        have he : 2*(m+1)+2=(2*m+2)+2 := by omega
        rw [he,Nat.pow_add]
        simp only [show (2:Nat)^2=4 by decide]
        omega
  have hp : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  rw [Nat.mul_add]
  omega

/-- All three high/low new infinite families are losslessly conjoined
    with the strongest existing exact source stopping criterion. -/
theorem blank_halts_iff_c70_both :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowedC70 m ∧
         BB6.Agent3ValSix.valSixMixedRootDecision 1
           (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedC70 j m ∧
         BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
           (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [blank_halts_iff_c70]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
      have hr : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff _ _).mp hroot
      have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
        dsimp [k]
        have hc := Nat.sub_add_cancel (high_bound_C70 j m)
        omega
      have hnot : ¬((j%128=63 ∧ m%128=82) ∨
                    (j%128=127 ∧ m%128=18)) := by
        intro hres
        exact (blank_no_high_63_82_or_127_18 j m k hres hstop) hr
      exact Or.inr ⟨j,m,⟨hprior,hnot⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

#print axioms blank_halts_iff_c70_both

#print axioms prior_low_admits_18
#print axioms blank_halts_iff_c70
end BB6.Agent20C70
