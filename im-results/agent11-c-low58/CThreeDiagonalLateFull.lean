import CThreeDiagonalJoint
import ValSixC58LateFast
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11DiagonalLate

/-- The entire odd diagonal survives both previously source-certified
    arbitrary inverse-depth high gates: their parameter parity guards
    require odd m, whereas the diagonal requires even m. -/
theorem prior_late_high_admits_diagonal (j m : Nat)
    (hm : 2≤m) (hj : j%2=1)
    (hd : m%32=(j+25)%32) :
    BB6.Agent11LateFastWrapper.highAllowed j m := by
  have hprior := BB6.Agent11Diagonal.prior_high_admits_diagonal j m hm hj hd
  have hdy : ∀ r, ¬ BB6.Agent11GateDecision.gate r j m := by
    intro r
    rintro ⟨_,_,_,hm4,_⟩
    omega
  have hdyBool : BB6.Agent11FastDepthGate.candidateAllowedBool j m = true :=
    (BB6.Agent11FastDepthGate.candidateAllowedBool_iff j m).mpr hdy
  have hlate : ∀ r, ¬ BB6.Agent11LateDepthGate.gate r j m := by
    intro r
    rintro ⟨_,_,hm4,_,_⟩
    omega
  have hlateBool : BB6.Agent11LateDepthGate.allowedBool j m = true :=
    (BB6.Agent11LateDepthGate.allowedBool_iff j m).mpr hlate
  unfold BB6.Agent11LateFastWrapper.highAllowed
    BB6.Agent11C58Boolean.highAllowed
  exact ⟨⟨hprior,hdyBool⟩,hlateBool⟩

/-- Extend the strongest previously integrated original-source high
    parameter filter by the genuine blank-unreachable diagonal. -/
def highAllowed (j m : Nat) : Prop :=
  BB6.Agent11LateFastWrapper.highAllowed j m ∧
    ¬(2≤m ∧ j%2=1 ∧ m%32=(j+25)%32)

private theorem high_bound (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hp : 4*m+4 ≤ 2^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hpow : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hpow
  rw [Nat.mul_add]
  omega

/-- Lossless authentic blank Machine C halting equivalence integrating
    all C58, ValSix, older dyadic, late dyadic and odd diagonal gates.
    The remaining parameter existential is still unbounded. -/
theorem blank_halts_iff_late_diagonal :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11C58ValSix.lowAllowed m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent11LateFastWrapper.blank_halts_iff_c58_all_depth_late_fast]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
      have hr : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff (2*j+3) k).mp hroot
      obtain ⟨time,ht⟩ := hr
      have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
        dsimp [k]
        have hc := Nat.sub_add_cancel (high_bound j m)
        omega
      have hnot : ¬(2≤m ∧ j%2=1 ∧ m%32=(j+25)%32) := by
        rintro ⟨hm,hj,hd⟩
        by_cases hm4 : 4≤m
        · exact (BB6.Agent4Three.high_stop_odd_diagonal_mod32
            j m k time hm4 hj hd hstop) ht
        · have hm2 : m=2 := by omega
          subst m
          have hj9 : j%32=9 := by omega
          exact (BB6.Agent11Diagonal.diagonal_two_no_blank
            j k time hj9 hstop) ht
      exact Or.inr ⟨j,m,⟨hprior,hnot⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

/-- Strict all-parameter independence from the previous full late-depth
    criterion, rather than a finite transcription or sampled witness. -/
theorem diagonal_strict_late (j m : Nat)
    (hm : 2≤m) (hj : j%2=1)
    (hd : m%32=(j+25)%32) :
    BB6.Agent11LateFastWrapper.highAllowed j m ∧ ¬highAllowed j m := by
  refine ⟨prior_late_high_admits_diagonal j m hm hj hd,?_⟩
  intro h
  exact h.2 ⟨hm,hj,hd⟩

#print axioms prior_late_high_admits_diagonal
#print axioms blank_halts_iff_late_diagonal
#print axioms diagonal_strict_late

end BB6.Agent11DiagonalLate
