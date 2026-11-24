import AffineConeLowStopAll
import ModularConeHighStop
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 4000000

namespace BB6.Agent42ModularCone

/-- The existing exact Machine C criterion strengthened by the
    sign-free modular inverse-cone sieve on the high stopping family. -/
def highAllowedModular (j m : Nat) : Prop :=
  BB6.Agent11SixAll.highAllowed j m ∧ highStopExcluded (j+1) m = false

theorem blank_halts_iff_modular :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent13AffineCone.lowAllowedAffine m ∧
        BB6.Agent11SixForced.sixForcedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedModular j m ∧
        BB6.Agent11SixForced.sixForcedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  constructor
  · intro hhalt
    have hcore := (BB6.Agent13AffineCone.blank_halts_iff_affine).mp hhalt
    rcases hcore with hlow | ⟨j,m,hprior,hroot⟩
    · exact Or.inl hlow
    · have hfilter : highStopExcluded (j+1) m = false := by
        cases hc : highStopExcluded (j+1) m with
        | false => rfl
        | true =>
          let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
          have hroot' : BB6.Agent11SixForced.sixForcedRootDecision (2*j+3) k = true := by
            simpa [k] using hroot
          have hr : BB6.Agent3.CReach (2*j+3) k :=
            (BB6.Agent11SixForced.sixForcedRootDecision_iff (2*j+3) k).mp hroot'
          have hbound : j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
            have hp : 4*m+4 ≤ 2^(2*m+2) :=
              BB6.Agent29New.power_linear_bound m
            have hpow : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
            have hj : j ≤ 2^(2*m+2)*j := by
              simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hpow
            rw [Nat.mul_add]
            omega
          have hstop : k+(j+1)+3*m+4 = 2^(2*m+2)*((j+1)+2) := by
            dsimp [k]
            calc
              (2^(2*m+2)*(j+3) - (j+3*m+5)) + (j+1)+3*m+4
                  = (2^(2*m+2)*(j+3) - (j+3*m+5)) + (j+3*m+5) := by omega
              _ = 2^(2*m+2)*(j+3) := Nat.sub_add_cancel hbound
              _ = 2^(2*m+2)*((j+1)+2) := by rfl
          exact (high_stop_excluded (j+1) m k (by omega) hstop hc) hr
      exact Or.inr ⟨j,m,⟨hprior,hfilter⟩,hroot⟩
  · intro h
    rcases h with hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩
    · exact (BB6.Agent13AffineCone.blank_halts_iff_affine).mpr (Or.inl hlow)
    · exact (BB6.Agent13AffineCone.blank_halts_iff_affine).mpr (Or.inr ⟨j,m,hprior,hroot⟩)

#print axioms blank_halts_iff_modular

end BB6.Agent42ModularCone
