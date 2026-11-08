import HighEvenRightC23FullForcedResidual
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent3M0FullForced

/-- On the m=0 high stopping line and j=3 mod 8, the original affine
    predecessor sends the target to an odd-right state with forbidden
    blank-image sum residue. -/
private theorem affine_normalize_m0_j3_mod8 (t : Nat) :
    BB6.Agent15.affineNormalize (16*t+9) (24*t+16) =
      (40*t+23,12*t+7) := by
  have hgate :
      4≤24*t+16 ∧ (24*t+16)%2=0 ∧
        ((16*t+9)+(24*t+16))%4=1 := by
    omega
  have hnot :
      ¬(4≤12*t+7 ∧ (12*t+7)%2=0 ∧
        ((40*t+23)+(12*t+7))%4=1) := by
    omega
  unfold BB6.Agent15.affineNormalize
  rw [dif_pos hgate]
  have hx : 16*t+9+(24*t+16)-2=40*t+23 := by omega
  have hk : (24*t+16-2)/2=12*t+7 := by omega
  rw [hx,hk]
  unfold BB6.Agent15.affineNormalize
  rw [dif_neg hnot]

/-- The four-sector full-forced normalizer takes exactly one affine
    predecessor on this infinite progression and then stops. -/
private theorem full_forced_normalize_m0_j3_mod8 (t : Nat) :
    BB6.Agent3.fullForcedNormalize (16*t+9) (24*t+16) =
      (40*t+23,12*t+7) := by
  have hO : ¬ BB6.Agent3.oddLowGate (16*t+9) (24*t+16) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS : ¬ BB6.Agent3.evenSevenGate (16*t+9) (24*t+16) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA : BB6.Agent3.evenAffineGate (16*t+9) (24*t+16) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hO' : ¬ BB6.Agent3.oddLowGate (40*t+23) (12*t+7) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS' : ¬ BB6.Agent3.evenSevenGate (40*t+23) (12*t+7) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA' : ¬ BB6.Agent3.evenAffineGate (40*t+23) (12*t+7) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE' : ¬ BB6.Agent46.sixEvenRightGate (40*t+23) (12*t+7) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO, dif_neg hS, dif_pos hA]
  have hx : 16*t+9+(24*t+16)-2=40*t+23 := by omega
  have hy : (24*t+16-2)/2=12*t+7 := by omega
  rw [hx,hy]
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO', dif_neg hS', dif_neg hA', dif_neg hE']

private theorem full_forced_excluded_m0_j3_mod8 (t : Nat) :
    BB6.Agent3.fullForcedExcluded (16*t+9) (24*t+16)=true := by
  simp [BB6.Agent3.fullForcedExcluded,
    full_forced_normalize_m0_j3_mod8]
  omega

/-- The whole infinite progression survives the previous C70+C23+
    all-phase+even-right high sieve. Only the new full-forced filter
    removes it. -/
theorem prior_high_allowed_m0_j3_mod8 (t : Nat) :
    BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight (8*t+3) 0 := by
  let j := 8*t+3
  have hbase : BB6.Agent3.jointHighAllowed j 0 := by
    unfold BB6.Agent3.jointHighAllowed
    dsimp [j]
    refine ⟨?_,?_,?_,?_,?_⟩ <;> omega
  have hrect : BB6.Agent3.jointHighRectAllowed j 0 := by
    unfold BB6.Agent3.jointHighRectAllowed
    exact ⟨hbase,by dsimp [j]; omega⟩
  have hOld : ∀ n : Nat, ¬(n+4≤2*0+2 ∧
      (j+3*0+3)%2^(n+4)=2^(n+2) ∧
      (2*j+3)%8=(if n%2=0 then 7 else 3)) := by
    intro n
    omega
  have hAgent19 : BB6.Agent19Joint.highAllowed j 0 := by
    unfold BB6.Agent19Joint.highAllowed
    exact ⟨hrect,hOld,by omega,by omega,by omega,by omega⟩
  have hAgent29 : BB6.Agent29Joint.highAllowedPlus j 0 := by
    unfold BB6.Agent29Joint.highAllowedPlus
    exact ⟨hAgent19,by omega,by omega,by omega,by omega⟩
  have hValSix : BB6.Agent3ValSix.highAllowedValSixThree j 0 := by
    unfold BB6.Agent3ValSix.highAllowedValSixThree
      BB6.Agent3ValSix.highAllowedValSix
    exact ⟨⟨hAgent29,by omega,by omega⟩,by omega⟩
  have hAgent11 : BB6.Agent11Joint.highAllowed j 0 := by
    unfold BB6.Agent11Joint.highAllowed
    exact ⟨hAgent19,by omega,by omega⟩
  have hFive : BB6.Agent19Five.highAllowed j 0 := by
    unfold BB6.Agent19Five.highAllowed
    exact ⟨hAgent11,by omega⟩
  have hright0 :
      (BB6.Agent15.affineNormalize (16*t+9) (24*t+16)).2≠4 := by
    rw [affine_normalize_m0_j3_mod8]
    omega
  have hx : 2*j+3=16*t+9 := by
    dsimp [j]
    omega
  have hy : 2^(2*0+2)*(j+3)-(j+3*0+5)=24*t+16 := by
    dsimp [j]
    omega
  have hright :
      (BB6.Agent15.affineNormalize (2*j+3)
        (2^(2*0+2)*(j+3)-(j+3*0+5))).2≠4 := by
    rw [hx,hy]
    exact hright0
  have hValFull : BB6.Agent3ValSix.highAllowedValSixFull j 0 := by
    unfold BB6.Agent3ValSix.highAllowedValSixFull
    exact ⟨hValSix,hFive,by omega,by omega,by omega,hright⟩
  have hC58ValSix : BB6.Agent11C58ValSix.highAllowed j 0 := by
    unfold BB6.Agent11C58ValSix.highAllowed
    exact ⟨hValFull,by omega⟩
  have hC58 : ∀ r : Nat, ¬(2≤r ∧ 3≤0 ∧ r+4≤2*0+2 ∧
      0%4=(2*r+3)%4 ∧
      (j+9*0+14)%2^(r+4)=3*2^(r+2)) := by
    intro r
    omega
  have hAllDepth : BB6.Agent11C58AllDepth.highAllowed j 0 := by
    unfold BB6.Agent11C58AllDepth.highAllowed
    exact ⟨hC58ValSix,hC58⟩
  have hPhase : ¬ BB6.Agent46.allPhaseExcluded j 0 := by
    unfold BB6.Agent46.allPhaseExcluded
    rintro ⟨r,hr8,hrbound,_⟩
    omega
  have hPhaseHigh : BB6.Agent24Phase.highAllowed j 0 := by
    unfold BB6.Agent24Phase.highAllowed
    exact ⟨hAllDepth,hPhase⟩
  have hC70 : BB6.Agent20C70.highAllowedC70 j 0 := by
    unfold BB6.Agent20C70.highAllowedC70
    exact ⟨hPhaseHigh,by omega⟩
  have hC23 : BB6.Agent20C23.highAllowedC23 j 0 := by
    unfold BB6.Agent20C23.highAllowedC23
    exact ⟨hC70,by omega⟩
  unfold BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight
  exact ⟨hC23,by omega⟩

/-- A genuinely new infinite source-excluded family of high stopping
    targets, previously admitted by the strongest existing high sieve. -/
theorem m0_j_mod8_three_new_infinite_exclusion (t : Nat) :
    BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight (8*t+3) 0 ∧
    BB6.Agent3.fullForcedExcluded (16*t+9) (24*t+16)=true := by
  exact ⟨prior_high_allowed_m0_j3_mod8 t,
    full_forced_excluded_m0_j3_mod8 t⟩

/-- Consequently none of these exact high stopping targets is on the
    authentic blank-tape section orbit. -/
theorem m0_j_mod8_three_blank_unreachable (t : Nat) :
    ¬ BB6.Agent3.CReach (16*t+9) (24*t+16) := by
  intro hreach
  rcases hreach with ⟨time,hrun⟩
  exact (BB6.Agent3.fullForcedExcluded_sound
    (16*t+9) (24*t+16) (full_forced_excluded_m0_j3_mod8 t) time) hrun

/-- The new Boolean high residual rejects the entire progression. -/
theorem m0_j_mod8_three_new_bool_filter (t : Nat) :
    BB6.Agent3FullForcedResidual.highAllowedC23WithEvenRightFullForcedBool
      (8*t+3) 0 = false := by
  have hprior :
      BB6.Agent3FullForcedResidual.highAllowedC23WithEvenRightBool
        (8*t+3) 0 = true :=
    (BB6.Agent3FullForcedResidual.highAllowedC23WithEvenRightBool_iff
      (8*t+3) 0).mpr (prior_high_allowed_m0_j3_mod8 t)
  have hx :
      BB6.Agent3FullForcedResidual.highTargetX (8*t+3)=16*t+9 := by
    simp [BB6.Agent3FullForcedResidual.highTargetX]
    omega
  have hy :
      BB6.Agent3FullForcedResidual.highTargetY (8*t+3) 0=24*t+16 := by
    simp [BB6.Agent3FullForcedResidual.highTargetY]
    omega
  have hforced :
      BB6.Agent3.fullForcedExcluded
        (BB6.Agent3FullForcedResidual.highTargetX (8*t+3))
        (BB6.Agent3FullForcedResidual.highTargetY (8*t+3) 0)=true := by
    rw [hx,hy]
    exact full_forced_excluded_m0_j3_mod8 t
  simp [BB6.Agent3FullForcedResidual.highAllowedC23WithEvenRightFullForcedBool,
    hprior, hforced]

#print axioms prior_high_allowed_m0_j3_mod8
#print axioms m0_j_mod8_three_new_infinite_exclusion
#print axioms m0_j_mod8_three_blank_unreachable
#print axioms m0_j_mod8_three_new_bool_filter

end BB6.Agent3M0FullForced
