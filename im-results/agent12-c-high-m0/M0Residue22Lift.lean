import HighEvenRightC23FullForcedResidual
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent12M0Lift

/-- The m=0 high stopping target at j=534 survives the complete
    C70+C23+all-phase+even-right sieve. The modulus 8192 below is
    chosen to preserve that admission while lifting its exact
    full-forced inverse itinerary. -/
private theorem prior_high_allowed_m0_j8192_22 (t : Nat) :
    BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight (8192*t+534) 0 := by
  let j := 8192*t+534
  have hbase : BB6.Agent3.jointHighAllowed j 0 := by
    unfold BB6.Agent3.jointHighAllowed
    dsimp [j]
    refine ⟨?_,?_,?_,?_,?_⟩ <;> omega
  have hrect : BB6.Agent3.jointHighRectAllowed j 0 := by
    unfold BB6.Agent3.jointHighRectAllowed
    exact ⟨hbase, by dsimp [j]; omega⟩
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
      (BB6.Agent15.affineNormalize (2*j+3) (3*j+7)).2≠4 := by
    unfold BB6.Agent15.affineNormalize
    have hgate :
        ¬(4≤3*j+7 ∧ (3*j+7)%2=0 ∧
          ((2*j+3)+(3*j+7))%4=1) := by
      dsimp [j]
      omega
    rw [dif_neg hgate]
    omega
  have hy :
      2^(2*0+2)*(j+3)-(j+3*0+5)=3*j+7 := by
    norm_num
    omega
  have hright :
      (BB6.Agent15.affineNormalize (2*j+3)
        (2^(2*0+2)*(j+3)-(j+3*0+5))).2≠4 := by
    rw [hy]
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

/-- Exact six-gate normalization of the previously unclassified
    m=0 residue j=534. For j=8192*t+534, the successive source-certified
    inverse states are affine in t and end at an odd-right state with
    coordinate sum 1 modulo 4. -/
private theorem full_forced_normalize_m0_j8192_22 (t : Nat) :
    BB6.Agent3.fullForcedNormalize (16384*t+1071) (24576*t+1609) =
      (54944*t+3570,5296*t+343) := by
  have hO0 : BB6.Agent3.oddLowGate
      (16384*t+1071) (24576*t+1609) := by
    unfold BB6.Agent3.oddLowGate
    omega

  have hO1 : ¬ BB6.Agent3.oddLowGate
      (20480*t+1338) (22528*t+1472) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS1 : ¬ BB6.Agent3.evenSevenGate
      (20480*t+1338) (22528*t+1472) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA1 : ¬ BB6.Agent3.evenAffineGate
      (20480*t+1338) (22528*t+1472) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE1 : BB6.Agent46.sixEvenRightGate
      (20480*t+1338) (22528*t+1472) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega

  have hO2 : ¬ BB6.Agent3.oddLowGate
      (43008*t+2808) (11264*t+735) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS2 : BB6.Agent3.evenSevenGate
      (43008*t+2808) (11264*t+735) := by
    unfold BB6.Agent3.evenSevenGate
    omega

  have hO3 : BB6.Agent3.oddLowGate
      (27136*t+1769) (19200*t+1251) := by
    unfold BB6.Agent3.oddLowGate
    omega

  have hO4 : ¬ BB6.Agent3.oddLowGate
      (23168*t+1508) (21184*t+1378) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS4 : ¬ BB6.Agent3.evenSevenGate
      (23168*t+1508) (21184*t+1378) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA4 : ¬ BB6.Agent3.evenAffineGate
      (23168*t+1508) (21184*t+1378) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE4 : BB6.Agent46.sixEvenRightGate
      (23168*t+1508) (21184*t+1378) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega

  have hO5 : ¬ BB6.Agent3.oddLowGate
      (44352*t+2884) (10592*t+688) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS5 : ¬ BB6.Agent3.evenSevenGate
      (44352*t+2884) (10592*t+688) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA5 : ¬ BB6.Agent3.evenAffineGate
      (44352*t+2884) (10592*t+688) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE5 : BB6.Agent46.sixEvenRightGate
      (44352*t+2884) (10592*t+688) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega

  have hO6 : ¬ BB6.Agent3.oddLowGate
      (54944*t+3570) (5296*t+343) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS6 : ¬ BB6.Agent3.evenSevenGate
      (54944*t+3570) (5296*t+343) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA6 : ¬ BB6.Agent3.evenAffineGate
      (54944*t+3570) (5296*t+343) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE6 : ¬ BB6.Agent46.sixEvenRightGate
      (54944*t+3570) (5296*t+343) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega

  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_pos hO0]
  have hx1 : ((16384*t+1071)+(24576*t+1609)-4)/2 =
      20480*t+1338 := by omega
  have hy1 : ((16384*t+1071)+3*(24576*t+1609)-10)/4 =
      22528*t+1472 := by omega
  rw [hx1,hy1]

  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO1,dif_neg hS1,dif_neg hA1,dif_pos hE1]
  have hx2 : (20480*t+1338)+(22528*t+1472)-2 =
      43008*t+2808 := by omega
  have hy2 : (22528*t+1472-2)/2 = 11264*t+735 := by omega
  rw [hx2,hy2]

  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO2,dif_pos hS2]
  have hx3 : ((43008*t+2808)+(11264*t+735)-5)/2 =
      27136*t+1769 := by omega
  have hy3 : ((43008*t+2808)+3*(11264*t+735)-9)/4 =
      19200*t+1251 := by omega
  rw [hx3,hy3]

  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_pos hO3]
  have hx4 : ((27136*t+1769)+(19200*t+1251)-4)/2 =
      23168*t+1508 := by omega
  have hy4 : ((27136*t+1769)+3*(19200*t+1251)-10)/4 =
      21184*t+1378 := by omega
  rw [hx4,hy4]

  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO4,dif_neg hS4,dif_neg hA4,dif_pos hE4]
  have hx5 : (23168*t+1508)+(21184*t+1378)-2 =
      44352*t+2884 := by omega
  have hy5 : (21184*t+1378-2)/2 = 10592*t+688 := by omega
  rw [hx5,hy5]

  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO5,dif_neg hS5,dif_neg hA5,dif_pos hE5]
  have hx6 : (44352*t+2884)+(10592*t+688)-2 =
      54944*t+3570 := by omega
  have hy6 : (10592*t+688-2)/2 = 5296*t+343 := by omega
  rw [hx6,hy6]

  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO6,dif_neg hS6,dif_neg hA6,dif_neg hE6]

/-- The entire lifted progression is rejected by the source-exact
    four-sector full-forced filter. -/
private theorem full_forced_excluded_m0_j8192_22 (t : Nat) :
    BB6.Agent3.fullForcedExcluded (16384*t+1071) (24576*t+1609)=true := by
  simp [BB6.Agent3.fullForcedExcluded,
    full_forced_normalize_m0_j8192_22]
  omega

/-- A new infinite m=0 high-stopping family, disjoint from the eleven
    existing progressions: j=8192*t+534 is admitted by the previous
    C70+C23+all-phase+even-right sieve but excluded by the exact
    full-forced source normalizer. -/
theorem m0_j8192_22_new_infinite_exclusion (t : Nat) :
    BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight (8192*t+534) 0 ∧
    BB6.Agent3.fullForcedExcluded (16384*t+1071) (24576*t+1609)=true := by
  exact ⟨prior_high_allowed_m0_j8192_22 t,
    full_forced_excluded_m0_j8192_22 t⟩

/-- No target in this exact high-stopping family lies on the original
    blank-tape section orbit, at any time. -/
theorem m0_j8192_22_blank_unreachable (t : Nat) :
    ¬ BB6.Agent3.CReach (16384*t+1071) (24576*t+1609) := by
  intro hreach
  rcases hreach with ⟨time,hrun⟩
  exact (BB6.Agent3.fullForcedExcluded_sound
    (16384*t+1071) (24576*t+1609)
    (full_forced_excluded_m0_j8192_22 t) time) hrun

/-- The complete high residual Boolean filter removes the whole family. -/
theorem m0_j8192_22_full_forced_filter_false (t : Nat) :
    BB6.Agent3FullForcedResidual.highAllowedC23WithEvenRightFullForcedBool
      (8192*t+534) 0 = false := by
  have hprior :
      BB6.Agent3FullForcedResidual.highAllowedC23WithEvenRightBool
        (8192*t+534) 0 = true :=
    (BB6.Agent3FullForcedResidual.highAllowedC23WithEvenRightBool_iff
      (8192*t+534) 0).mpr (prior_high_allowed_m0_j8192_22 t)
  simp [BB6.Agent3FullForcedResidual.highAllowedC23WithEvenRightFullForcedBool,
    hprior,full_forced_excluded_m0_j8192_22]

#print axioms prior_high_allowed_m0_j8192_22
#print axioms full_forced_normalize_m0_j8192_22
#print axioms m0_j8192_22_new_infinite_exclusion
#print axioms m0_j8192_22_blank_unreachable
#print axioms m0_j8192_22_full_forced_filter_false

end BB6.Agent12M0Lift
