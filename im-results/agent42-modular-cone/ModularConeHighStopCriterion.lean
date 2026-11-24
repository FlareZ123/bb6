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
        | false => exact hc
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
              _ = 2^(2*m+2)*((j+1)+2) := by congr 1; omega
          exact (high_stop_excluded (j+1) m k (by omega) hstop hc) hr
      exact Or.inr ⟨j,m,⟨hprior,hfilter⟩,hroot⟩
  · intro h
    rcases h with hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩
    · exact (BB6.Agent13AffineCone.blank_halts_iff_affine).mpr (Or.inl hlow)
    · exact (BB6.Agent13AffineCone.blank_halts_iff_affine).mpr (Or.inr ⟨j,m,hprior,hroot⟩)

/-- Candidates outside the old relative-growth gate whose modular cone
    accepts. The source criterion decides which also survive the older
    highAllowed filter. -/
def outsideProbe : List (Nat × Nat) :=
  [(13,3),(14,3),(16,3),(17,3),(19,3),(20,3),(21,3),(22,3),(24,3),
   (25,3),(28,3),(29,3),(30,3),(32,3),(33,3),(35,3),(37,3),(38,3),
   (41,3),(43,3),(45,3),(46,3),(47,3),(49,3),(51,3),(53,3),(54,3),
   (57,3),(60,3),(61,3),(62,3)]

def strictOutsideProbe : List (Nat × Nat) :=
  outsideProbe.filter (fun p =>
    decide (BB6.Agent11SixAll.highAllowed p.1 p.2) &&
      highStopExcluded (p.1+1) p.2)

#eval strictOutsideProbe

#print axioms blank_halts_iff_modular

end BB6.Agent42ModularCone
