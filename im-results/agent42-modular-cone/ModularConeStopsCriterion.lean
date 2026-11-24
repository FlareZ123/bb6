import ModularConeHighStopCriterion
import ModularConeLowStop
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 4000000

namespace BB6.Agent42ModularCone

/-- The original low affine filter intersected with the independent
    sign-free modular inverse-cone exclusion. -/
def lowAllowedModular (m : Nat) : Prop :=
  BB6.Agent13AffineCone.lowAllowedAffine m ∧ lowStopExcluded m = false

/-- Exact Machine C halting criterion with the modular inverse-cone filter
    applied to both unified stopping families. The low branch uses j=0;
    the high branch uses unified j=j_original+1. -/
theorem blank_halts_iff_modular_both :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowedModular m ∧
        BB6.Agent11SixForced.sixForcedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedModular j m ∧
        BB6.Agent11SixForced.sixForcedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  constructor
  · intro hhalt
    have hcore := (blank_halts_iff_modular).mp hhalt
    rcases hcore with hlow | hhigh
    · rcases hlow with ⟨m,hlow,hroot⟩
      have hfilter : lowStopExcluded m = false := by
        cases hc : lowStopExcluded m with
        | false => rfl
        | true =>
          let k := 2^(2*m+3)-(3*m+4)
          have hroot' : BB6.Agent11SixForced.sixForcedRootDecision 1 k = true := by
            simpa [k] using hroot
          have hr : BB6.Agent3.CReach 1 k :=
            (BB6.Agent11SixForced.sixForcedRootDecision_iff 1 k).mp hroot'
          have hp : 4*m+4 ≤ P (2*m+2) := by
            simpa [P] using BB6.Agent29New.power_linear_bound m
          have hmul : 2*(4*m+4) ≤ 2*P (2*m+2) :=
            Nat.mul_le_mul_left 2 hp
          have hbound : 3*m+4 ≤ P (2*m+2)*2 := by
            calc
              3*m+4 ≤ 2*(4*m+4) := by omega
              _ ≤ 2*P (2*m+2) := hmul
              _ = P (2*m+2)*2 := by omega
          have hpow : P (2*m+2)*2 = 2^(2*m+3) := by
            unfold P
            rw [show 2*m+3=(2*m+2)+1 by omega, Nat.pow_succ]
            rfl
          have hbound' : 3*m+4 ≤ 2^(2*m+3) := by
            rw [← hpow]
            exact hbound
          have hstop : k+3*m+4 = P (2*m+2)*2 := by
            dsimp [k]
            rw [Nat.sub_add_cancel hbound']
            exact hpow.symm
          exact False.elim ((low_stop_excluded m k hstop hc) hr)
      exact Or.inl ⟨m,⟨hlow,hfilter⟩,hroot⟩
    · exact Or.inr hhigh
  · intro h
    rcases h with hlow | hhigh
    · rcases hlow with ⟨m,⟨hlow,_⟩,hroot⟩
      exact (blank_halts_iff_modular).mpr (Or.inl ⟨m,hlow,hroot⟩)
    · exact (blank_halts_iff_modular).mpr (Or.inr hhigh)

#print axioms blank_halts_iff_modular_both

end BB6.Agent42ModularCone
