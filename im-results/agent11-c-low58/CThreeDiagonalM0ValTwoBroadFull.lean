import CThreeDiagonalM0ValTwoFull
import M0ValTwoBroad
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11M0ValTwoBroadFull

/-- Add the complementary m=0 ray j=2055 modulo2048 that is
    admitted by the previous exact criterion (which already excluded
    j=1031 modulo2048). Their union is the entire j=7 modulo1024,
    j>=1031 broad source-certified valuation-two ray. -/
def highAllowed (j m : Nat) : Prop :=
  BB6.Agent11M0ValTwoFull.highAllowed j m ∧
  ¬(m=0 ∧ j%2048=7 ∧ 2055≤j)

private theorem high_bound (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hp : 4*m+4 ≤ 2^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hpow : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hpow
  rw [Nat.mul_add]
  omega

/-- Lossless original-blank Machine C halting iff after the two
    previous m=0 classes and the entire broad val-two family have
    been removed. The prior arbitrary-depth dyadic and diagonal gates
    are preserved. All remaining parameter searches are unbounded. -/
theorem blank_halts_iff_late_diagonal_mzero_broad :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11C58ValSix.lowAllowed m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent11M0ValTwoFull.blank_halts_iff_late_diagonal_mzero_three]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
      have hr : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff (2*j+3) k).mp hroot
      have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
        dsimp [k]
        have hc := Nat.sub_add_cancel (high_bound j m)
        omega
      have hnot : ¬(m=0 ∧ j%2048=7 ∧ 2055≤j) := by
        rintro ⟨hm,hj,hmin⟩
        subst m
        have hmod : j%1024=7 := by omega
        have hlo : 1031≤j := by omega
        exact (BB6.Agent11M0ValTwoBroad.high_stop_mzero_7mod1024
          j k hmod hlo hstop) hr
      exact Or.inr ⟨j,m,⟨hprior,hnot⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

/-- Strict old-sieve independence on *every* parameter of the
    complementary subray. Together with the previously strict
    j=1031 modulo2048 class, this establishes the entire broad family. -/
theorem broad_complement_strict (q : Nat) :
    BB6.Agent11M0ValTwoFull.highAllowed (2055+2048*q) 0 ∧
      ¬highAllowed (2055+2048*q) 0 := by
  have hlate : BB6.Agent11DiagonalLate.highAllowed (2055+2048*q) 0 :=
    BB6.Agent11M0DeepFull.prior_late_diagonal_admits_mzero_three
      (2055+2048*q) (by omega)
  have hfirst : ¬((0:Nat)=0 ∧ (2055+2048*q)%128=71) := by omega
  have hsecond : ¬((0:Nat)=0 ∧ (2055+2048*q)%2048=1159) := by omega
  have hthird : ¬((0:Nat)=0 ∧ (2055+2048*q)%2048=1031) := by omega
  have hprior : BB6.Agent11M0ValTwoFull.highAllowed (2055+2048*q) 0 :=
    ⟨⟨⟨hlate,hfirst⟩,hsecond⟩,hthird⟩
  refine ⟨hprior,?_⟩
  intro h
  exact h.2 ⟨rfl,by omega,by omega⟩

#print axioms blank_halts_iff_late_diagonal_mzero_broad
#print axioms broad_complement_strict

end BB6.Agent11M0ValTwoBroadFull
