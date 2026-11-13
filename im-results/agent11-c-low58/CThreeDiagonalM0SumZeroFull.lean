import CThreeSixAllCriterion
import M0EvenEvenSumZeroRays
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11M0SumZeroAll

/-- Strengthen the latest exact six-sector high stopping predicate by
    removing the two source-proven m=0 sum-zero rays. The low branch and
    all prior C58, dyadic, diagonal, m=0, and six-sector filters remain. -/
def highAllowed (j m : Nat) : Prop :=
  BB6.Agent11SixAll.highAllowed j m ∧
  ¬(m=0 ∧ j%2048=1895) ∧
  ¬(m=0 ∧ j%8192=359)

private theorem high_bound (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hp : 4*m+4 ≤ 2^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hpow : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hpow
  rw [Nat.mul_add]
  omega

/-- Lossless exact original-blank Machine C halting iff after excluding
    both newly closed m=0 high-stop families from the latest six-sector
    criterion. Both parameter existentials remain unbounded. -/
theorem blank_halts_iff_six_mzero_sumzero :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11SixAll.lowAllowed m ∧
        BB6.Agent11SixForced.sixForcedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
        BB6.Agent11SixForced.sixForcedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent11SixAll.blank_halts_iff_six_both]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
      have hr : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent11SixForced.sixForcedRootDecision_iff (2*j+3) k).mp hroot
      have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
        dsimp [k]
        have hc := Nat.sub_add_cancel (high_bound j m)
        omega
      have hnot1895 : ¬(m=0 ∧ j%2048=1895) := by
        rintro ⟨hm,hj⟩
        subst m
        exact BB6.Agent11M0SumZero.high_stop_mzero_1895 j k hj hstop hr
      have hnot359 : ¬(m=0 ∧ j%8192=359) := by
        rintro ⟨hm,hj⟩
        subst m
        exact BB6.Agent11M0SumZero.high_stop_mzero_359 j k hj hstop hr
      exact Or.inr ⟨j,m,⟨hprior,hnot1895,hnot359⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

#print axioms blank_halts_iff_six_mzero_sumzero

end BB6.Agent11M0SumZeroAll
