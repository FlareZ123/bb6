import SixForcedNormalize
import CThreeDiagonalM0DeepFull
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11SixCriterion

/-- Stronger global high stopping predicate: exclude any original Machine C
    target whose exact six-source inverse normalization terminates at the
    genuine blank-image parity obstruction. Unlike a modular ray gate,
    this test is unbounded, recursive, and applies to ALL j and m. -/
def highAllowed (j m : Nat) : Prop :=
  BB6.Agent11M0DeepFull.highAllowed j m ∧
  BB6.Agent11SixForced.sixForcedExcluded (2*j+3)
    (2^(2*m+2)*(j+3)-(j+3*m+5))=false

private theorem high_bound (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hp : 4*m+4 ≤ 2^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hpow : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hpow
  rw [Nat.mul_add]
  omega

/-- Exact full original-blank Machine C halting criterion with all
    earlier ValSix+C58+arbitrary-depth+diagonal+two m0-ray restrictions,
    strengthened by a source-certified recursive six-sector root sieve. -/
theorem blank_halts_iff_six_forced :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11C58ValSix.lowAllowed m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent11M0DeepFull.blank_halts_iff_late_diagonal_mzero_two]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
      have hr : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff (2*j+3) k).mp hroot
      have hfilter :
          BB6.Agent11SixForced.sixForcedExcluded (2*j+3) k = false := by
        cases hh : BB6.Agent11SixForced.sixForcedExcluded (2*j+3) k with
        | false => rfl
        | true =>
            exact False.elim
              ((BB6.Agent11SixForced.sixForcedExcluded_sound
                (2*j+3) k hh) hr)
      exact Or.inr ⟨j,m,⟨hprior,hfilter⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

/-- The genuinely new inverse-sector filter rejects a concrete original
    m=0 stopping parameter admitted by the entire previous full criterion.
    An independent theorem M0OddRayValTwo proves an infinite extension. -/
set_option maxRecDepth 8192 in
theorem six_forced_rejects_1031 :
    BB6.Agent11SixForced.sixForcedExcluded 2065 3100=true := by
  decide

theorem six_forced_strict_1031 :
    BB6.Agent11M0DeepFull.highAllowed 1031 0 ∧
      ¬highAllowed 1031 0 := by
  have hprior :
      BB6.Agent11DiagonalLate.highAllowed 1031 0 :=
    BB6.Agent11M0DeepFull.prior_late_diagonal_admits_mzero_three
      1031 (by decide)
  have hfirst : ¬((0:Nat)=0 ∧ 1031%128=71) := by decide
  have hsecond : ¬((0:Nat)=0 ∧ 1031%2048=1159) := by decide
  have hprev : BB6.Agent11M0DeepFull.highAllowed 1031 0 :=
    ⟨⟨hprior,hfirst⟩,hsecond⟩
  refine ⟨hprev,?_⟩
  intro h
  have heq : (2:Nat)^(2*0+2)*(1031+3)-(1031+3*0+5) = 3100 := by decide
  have hh : BB6.Agent11SixForced.sixForcedExcluded 2065 3100=false := by
    simpa only [heq] using h.2
  exact (by have ht := six_forced_rejects_1031; omega : False)

#print axioms blank_halts_iff_six_forced
#print axioms six_forced_rejects_1031
#print axioms six_forced_strict_1031

end BB6.Agent11SixCriterion
