import CThreeDiagonalM0Full
import M0OddRayDeep
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11M0DeepFull

/-- The complete previously merged all-depth + diagonal high parameter
    domain admits every m=0, j=3 modulo4 stopping parameter.
    This proves strictness of further m=0 inverse-ray source exclusions
    without relying on isolated numerical witnesses. -/
theorem prior_late_diagonal_admits_mzero_three (j : Nat)
    (hj : j%4=3) :
    BB6.Agent11DiagonalLate.highAllowed j 0 := by
  have hbase : BB6.Agent3.jointHighAllowed j 0 := by
    unfold BB6.Agent3.jointHighAllowed
    refine ⟨?_,?_,?_,?_,?_⟩ <;> omega
  have hrect : BB6.Agent3.jointHighRectAllowed j 0 := by
    unfold BB6.Agent3.jointHighRectAllowed
    exact ⟨hbase,by omega⟩
  have hdy : ∀ n, ¬(n+4≤2*0+2 ∧
      (j+3*0+3)%2^(n+4)=2^(n+2) ∧
      (2*j+3)%8=(if n%2=0 then 7 else 3)) := by
    intro n
    rintro ⟨hn,_,_⟩
    omega
  have h19 : BB6.Agent19Joint.highAllowed j 0 := by
    unfold BB6.Agent19Joint.highAllowed
    exact ⟨hrect,hdy,by omega,by omega,by omega,by omega⟩
  have h29 : BB6.Agent29Joint.highAllowedPlus j 0 := by
    unfold BB6.Agent29Joint.highAllowedPlus
    exact ⟨h19,by omega,by omega,by omega,by omega⟩
  have hval : BB6.Agent3ValSix.highAllowedValSixThree j 0 := by
    unfold BB6.Agent3ValSix.highAllowedValSixThree
      BB6.Agent3ValSix.highAllowedValSix
    exact ⟨⟨h29,by omega,by omega⟩,by omega⟩
  have h11 : BB6.Agent11Joint.highAllowed j 0 := by
    unfold BB6.Agent11Joint.highAllowed
    exact ⟨h19,by omega,by omega⟩
  have hf : BB6.Agent19Five.highAllowed j 0 := by
    unfold BB6.Agent19Five.highAllowed
    exact ⟨h11,by omega⟩
  have hk : (2^(2*0+2)*(j+3)-(j+3*0+5))=3*j+7 := by
    have hp : (2:Nat)^(2*0+2)=4 := by decide
    rw [hp]
    omega
  have hright : (BB6.Agent15.affineNormalize (2*j+3)
      (2^(2*0+2)*(j+3)-(j+3*0+5))).2≠4 := by
    rw [hk]
    exact BB6.Agent11Diagonal.norm_right_ne_four (2*j+3) (3*j+7)
      (by omega) (by omega)
  have hfull : BB6.Agent3ValSix.highAllowedValSixFull j 0 := by
    unfold BB6.Agent3ValSix.highAllowedValSixFull
    exact ⟨hval,hf,by omega,by omega,by omega,hright⟩
  have hc58 : BB6.Agent11C58ValSix.highAllowed j 0 := by
    unfold BB6.Agent11C58ValSix.highAllowed
    exact ⟨hfull,by omega⟩
  have hgate : ∀ r, ¬ BB6.Agent11GateDecision.gate r j 0 := by
    intro r
    rintro ⟨_,h3,_,_,_⟩
    omega
  have hgateBool : BB6.Agent11FastDepthGate.candidateAllowedBool j 0 =true :=
    (BB6.Agent11FastDepthGate.candidateAllowedBool_iff j 0).mpr hgate
  have hlate : ∀ r, ¬ BB6.Agent11LateDepthGate.gate r j 0 := by
    intro r
    rintro ⟨_,h3,_,_,_⟩
    omega
  have hlateBool : BB6.Agent11LateDepthGate.allowedBool j 0 =true :=
    (BB6.Agent11LateDepthGate.allowedBool_iff j 0).mpr hlate
  have hdiag : ¬(2≤(0:Nat) ∧ j%2=1 ∧ (0:Nat)%32=(j+25)%32) := by
    omega
  unfold BB6.Agent11DiagonalLate.highAllowed
    BB6.Agent11LateFastWrapper.highAllowed
    BB6.Agent11C58Boolean.highAllowed
  exact ⟨⟨⟨hc58,hgateBool⟩,hlateBool⟩,hdiag⟩

/-- Preserve the full previous high filter, including the m=0 j=71
    modulo128 ray, and source-exclude an independent j=1159 modulo2048
    high stopping ray at the same m=0 layer. -/
def highAllowed (j m : Nat) : Prop :=
  BB6.Agent11DiagonalM0.highAllowed j m ∧
    ¬(m=0 ∧ j%2048=1159)

private theorem high_bound (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hp : 4*m+4 ≤ 2^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hpow : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hpow
  rw [Nat.mul_add]
  omega

/-- Entire original-blank Machine C halting iff with the late-depth,
    m>=2 diagonal and TWO distinct m=0 exact inverse-ray obstructions. -/
theorem blank_halts_iff_late_diagonal_mzero_two :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11C58ValSix.lowAllowed m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent11DiagonalM0.blank_halts_iff_late_diagonal_mzero]
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
      have hnot : ¬(m=0 ∧ j%2048=1159) := by
        rintro ⟨hm,hj⟩
        subst m
        exact (BB6.Agent11M0Deep.high_stop_mzero_1159 j k hj hstop) hr
      exact Or.inr ⟨j,m,⟨hprior,hnot⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

/-- Deep-ray parameters survived every previous joint source filter,
    including the already excluded m=0 j=71 mod128 ray. -/
theorem deep_ray_strict (q : Nat) :
    BB6.Agent11DiagonalM0.highAllowed (1159+2048*q) 0 ∧
    ¬highAllowed (1159+2048*q) 0 := by
  have hprior : BB6.Agent11DiagonalLate.highAllowed (1159+2048*q) 0 :=
    prior_late_diagonal_admits_mzero_three (1159+2048*q) (by omega)
  have hfirst : ¬((0:Nat)=0 ∧ (1159+2048*q)%128=71) := by omega
  have hprev : BB6.Agent11DiagonalM0.highAllowed (1159+2048*q) 0 :=
    ⟨hprior,hfirst⟩
  refine ⟨hprev,?_⟩
  intro h
  exact h.2 ⟨rfl,by omega⟩

#print axioms prior_late_diagonal_admits_mzero_three
#print axioms blank_halts_iff_late_diagonal_mzero_two
#print axioms deep_ray_strict

end BB6.Agent11M0DeepFull
