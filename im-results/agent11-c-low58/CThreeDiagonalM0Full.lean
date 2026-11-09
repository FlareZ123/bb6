import CThreeDiagonalLateFull
import M0OddRay
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11DiagonalM0

/-- Every high stopping target at m=0, j=71 modulo128 survives
    the entire previously merged ValSix+C58+late-depth+diagonal filter.
    Consequently the source-excluded m=0 ray is strictly new. -/
theorem previous_late_diagonal_admits_mzero_71 (q : Nat) :
    BB6.Agent11DiagonalLate.highAllowed (71+128*q) 0 := by
  let j := 71+128*q
  have hbase : BB6.Agent3.jointHighAllowed j 0 := by
    unfold BB6.Agent3.jointHighAllowed
    refine ⟨?_,?_,?_,?_,?_⟩ <;> dsimp [j] <;> omega
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
    exact ⟨h19,by dsimp [j]; omega,by omega⟩
  have hf : BB6.Agent19Five.highAllowed j 0 := by
    unfold BB6.Agent19Five.highAllowed
    exact ⟨h11,by omega⟩
  have hk : (2^(2*0+2)*(j+3)-(j+3*0+5))=220+384*q := by
    dsimp [j]
    omega
  have hright : (BB6.Agent15.affineNormalize (2*j+3)
      (2^(2*0+2)*(j+3)-(j+3*0+5))).2≠4 := by
    rw [hk]
    exact BB6.Agent11Diagonal.norm_right_ne_four (2*j+3) (220+384*q)
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

/-- Full prior original-source high gate plus a second genuinely
    independent m=0 infinite source-inverse stopping obstruction. -/
def highAllowed (j m : Nat) : Prop :=
  BB6.Agent11DiagonalLate.highAllowed j m ∧
    ¬(m=0 ∧ j%128=71)

private theorem high_bound (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hp : 4*m+4 ≤ 2^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hpow : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hpow
  rw [Nat.mul_add]
  omega

/-- Lossless authenticated blank-halting criterion, removing the
    full source-verified odd diagonal and the additional infinite m=0 ray.
    The unrestricted global parameter existence remains unresolved. -/
theorem blank_halts_iff_late_diagonal_mzero :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11C58ValSix.lowAllowed m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent11DiagonalLate.blank_halts_iff_late_diagonal]
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
      have hnot : ¬(m=0 ∧ j%128=71) := by
        rintro ⟨hm,hj⟩
        subst m
        exact (BB6.Agent11M0Ray.high_stop_mzero_71 j k hj hstop) hr
      exact Or.inr ⟨j,m,⟨hprior,hnot⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

theorem mzero_71_strict (q : Nat) :
    BB6.Agent11DiagonalLate.highAllowed (71+128*q) 0 ∧
      ¬highAllowed (71+128*q) 0 := by
  refine ⟨previous_late_diagonal_admits_mzero_71 q,?_⟩
  intro h
  exact h.2 ⟨rfl,by omega⟩

#print axioms previous_late_diagonal_admits_mzero_71
#print axioms blank_halts_iff_late_diagonal_mzero
#print axioms mzero_71_strict

end BB6.Agent11DiagonalM0
