import HighEvenRightC23FullForcedResidual
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent19M0Additional

/-- Five further m=0 residue progressions found by the exact finite
    FullForcedParamScan. Their witnesses are now parameterized below. -/
private def m0AdditionalFamily (j : Nat) : Prop :=
  (∃ t, j=32*t+6) ∨
  (∃ t, j=64*t+58) ∨
  (∃ t, j=32*t+21) ∨
  (∃ t, j=32*t+15) ∨
  (∃ t, j=128*t+71)

/-- All five progressions are admitted by the complete preceding
    C70+C23+all-phase+even-right high sieve. -/
private theorem prior_high_allowed_m0_of_family (j : Nat)
    (hf : m0AdditionalFamily j) :
    BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight j 0 := by
  rcases hf with ⟨t,hj⟩ | ⟨t,hj⟩ | ⟨t,hj⟩ | ⟨t,hj⟩ | ⟨t,hj⟩
  all_goals
    have hbase : BB6.Agent3.jointHighAllowed j 0 := by
      unfold BB6.Agent3.jointHighAllowed
      refine ⟨?_,?_,?_,?_,?_⟩ <;> omega
    have hrect : BB6.Agent3.jointHighRectAllowed j 0 := by
      unfold BB6.Agent3.jointHighRectAllowed
      exact ⟨hbase,by omega⟩
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
      by_cases hgate :
          4≤3*j+7 ∧ (3*j+7)%2=0 ∧
            ((2*j+3)+(3*j+7))%4=1
      · rw [dif_pos hgate]
        omega
      · rw [dif_neg hgate]
        omega
    have hright :
        (BB6.Agent15.affineNormalize (2*j+3)
          (2^(2*0+2)*(j+3)-(j+3*0+5))).2≠4 := by
      simpa using hright0
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

/-- j=32t+6: odd-low inverse, then six-even-right inverse. -/
private theorem full_forced_normalize_m0_j32_six (t : Nat) :
    BB6.Agent3.fullForcedNormalize (64*t+15) (96*t+25) =
      (168*t+36,44*t+9) := by
  have hO : BB6.Agent3.oddLowGate (64*t+15) (96*t+25) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hO1 : ¬ BB6.Agent3.oddLowGate (80*t+18) (88*t+20) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS1 : ¬ BB6.Agent3.evenSevenGate (80*t+18) (88*t+20) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA1 : ¬ BB6.Agent3.evenAffineGate (80*t+18) (88*t+20) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE1 : BB6.Agent46.sixEvenRightGate (80*t+18) (88*t+20) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  have hO2 : ¬ BB6.Agent3.oddLowGate (168*t+36) (44*t+9) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS2 : ¬ BB6.Agent3.evenSevenGate (168*t+36) (44*t+9) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA2 : ¬ BB6.Agent3.evenAffineGate (168*t+36) (44*t+9) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE2 : ¬ BB6.Agent46.sixEvenRightGate (168*t+36) (44*t+9) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_pos hO]
  have hx1 : ((64*t+15)+(96*t+25)-4)/2=80*t+18 := by omega
  have hy1 : ((64*t+15)+3*(96*t+25)-10)/4=88*t+20 := by omega
  rw [hx1,hy1]
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO1,dif_neg hS1,dif_neg hA1,dif_pos hE1]
  have hx2 : (80*t+18)+(88*t+20)-2=168*t+36 := by omega
  have hy2 : (88*t+20-2)/2=44*t+9 := by omega
  rw [hx2,hy2]
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO2,dif_neg hS2,dif_neg hA2,dif_neg hE2]

private theorem full_forced_excluded_m0_j32_six (t : Nat) :
    BB6.Agent3.fullForcedExcluded (64*t+15) (96*t+25)=true := by
  simp [BB6.Agent3.fullForcedExcluded,
    full_forced_normalize_m0_j32_six]
  omega

/-- j=64t+58: odd-low inverse, then even-seven inverse. -/
private theorem full_forced_normalize_m0_j64_fiftyeight (t : Nat) :
    BB6.Agent3.fullForcedNormalize (128*t+119) (192*t+181) =
      (168*t+153,172*t+157) := by
  have hO : BB6.Agent3.oddLowGate (128*t+119) (192*t+181) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hO1 : ¬ BB6.Agent3.oddLowGate (160*t+148) (176*t+163) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS1 : BB6.Agent3.evenSevenGate (160*t+148) (176*t+163) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA1 : ¬ BB6.Agent3.evenAffineGate (160*t+148) (176*t+163) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE1 : ¬ BB6.Agent46.sixEvenRightGate (160*t+148) (176*t+163) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  have hO2 : ¬ BB6.Agent3.oddLowGate (168*t+153) (172*t+157) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS2 : ¬ BB6.Agent3.evenSevenGate (168*t+153) (172*t+157) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA2 : ¬ BB6.Agent3.evenAffineGate (168*t+153) (172*t+157) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE2 : ¬ BB6.Agent46.sixEvenRightGate (168*t+153) (172*t+157) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_pos hO]
  have hx1 : ((128*t+119)+(192*t+181)-4)/2=160*t+148 := by omega
  have hy1 : ((128*t+119)+3*(192*t+181)-10)/4=176*t+163 := by omega
  rw [hx1,hy1]
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO1,dif_pos hS1]
  have hy2 : ((160*t+148)+3*(176*t+163)-9)/4=172*t+157 := by omega
  rw [hy2]
  have hx2 : ((160*t+148)+(176*t+163)-5)/2=168*t+153 := by omega
  rw [hx2]
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO2,dif_neg hS2,dif_neg hA2,dif_neg hE2]

private theorem full_forced_excluded_m0_j64_fiftyeight (t : Nat) :
    BB6.Agent3.fullForcedExcluded (128*t+119) (192*t+181)=true := by
  simp [BB6.Agent3.fullForcedExcluded,
    full_forced_normalize_m0_j64_fiftyeight]
  omega

/-- j=32t+21: two six-even-right inverses, then the even-affine inverse. -/
private theorem full_forced_normalize_m0_j32_twentyone (t : Nat) :
    BB6.Agent3.fullForcedNormalize (64*t+45) (96*t+70) =
      (232*t+159,12*t+7) := by
  have hO0 : ¬ BB6.Agent3.oddLowGate (64*t+45) (96*t+70) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS0 : ¬ BB6.Agent3.evenSevenGate (64*t+45) (96*t+70) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA0 : ¬ BB6.Agent3.evenAffineGate (64*t+45) (96*t+70) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE0 : BB6.Agent46.sixEvenRightGate (64*t+45) (96*t+70) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  have hO1 : ¬ BB6.Agent3.oddLowGate (160*t+113) (48*t+34) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS1 : ¬ BB6.Agent3.evenSevenGate (160*t+113) (48*t+34) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA1 : ¬ BB6.Agent3.evenAffineGate (160*t+113) (48*t+34) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE1 : BB6.Agent46.sixEvenRightGate (160*t+113) (48*t+34) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  have hO2 : ¬ BB6.Agent3.oddLowGate (208*t+145) (24*t+16) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS2 : ¬ BB6.Agent3.evenSevenGate (208*t+145) (24*t+16) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA2 : BB6.Agent3.evenAffineGate (208*t+145) (24*t+16) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hO3 : ¬ BB6.Agent3.oddLowGate (232*t+159) (12*t+7) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS3 : ¬ BB6.Agent3.evenSevenGate (232*t+159) (12*t+7) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA3 : ¬ BB6.Agent3.evenAffineGate (232*t+159) (12*t+7) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE3 : ¬ BB6.Agent46.sixEvenRightGate (232*t+159) (12*t+7) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO0,dif_neg hS0,dif_neg hA0,dif_pos hE0]
  have hx1 : (64*t+45)+(96*t+70)-2=160*t+113 := by omega
  have hy1 : (96*t+70-2)/2=48*t+34 := by omega
  rw [hx1,hy1]
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO1,dif_neg hS1,dif_neg hA1,dif_pos hE1]
  have hx2 : (160*t+113)+(48*t+34)-2=208*t+145 := by omega
  have hy2 : (48*t+34-2)/2=24*t+16 := by omega
  rw [hx2,hy2]
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO2,dif_neg hS2,dif_pos hA2]
  have hx3 : (208*t+145)+(24*t+16)-2=232*t+159 := by omega
  have hy3 : (24*t+16-2)/2=12*t+7 := by omega
  rw [hx3,hy3]
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO3,dif_neg hS3,dif_neg hA3,dif_neg hE3]

private theorem full_forced_excluded_m0_j32_twentyone (t : Nat) :
    BB6.Agent3.fullForcedExcluded (64*t+45) (96*t+70)=true := by
  simp [BB6.Agent3.fullForcedExcluded,
    full_forced_normalize_m0_j32_twentyone]
  omega

/-- j=32t+15: even-affine inverse, then odd-low inverse. -/
private theorem full_forced_normalize_m0_j32_fifteen (t : Nat) :
    BB6.Agent3.fullForcedNormalize (64*t+33) (96*t+52) =
      (104*t+52,76*t+37) := by
  have hO0 : ¬ BB6.Agent3.oddLowGate (64*t+33) (96*t+52) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS0 : ¬ BB6.Agent3.evenSevenGate (64*t+33) (96*t+52) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA0 : BB6.Agent3.evenAffineGate (64*t+33) (96*t+52) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hO1 : BB6.Agent3.oddLowGate (160*t+83) (48*t+25) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS1 : ¬ BB6.Agent3.evenSevenGate (160*t+83) (48*t+25) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA1 : ¬ BB6.Agent3.evenAffineGate (160*t+83) (48*t+25) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE1 : ¬ BB6.Agent46.sixEvenRightGate (160*t+83) (48*t+25) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  have hO2 : ¬ BB6.Agent3.oddLowGate (104*t+52) (76*t+37) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS2 : ¬ BB6.Agent3.evenSevenGate (104*t+52) (76*t+37) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA2 : ¬ BB6.Agent3.evenAffineGate (104*t+52) (76*t+37) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE2 : ¬ BB6.Agent46.sixEvenRightGate (104*t+52) (76*t+37) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO0,dif_neg hS0,dif_pos hA0]
  have hx1 : (64*t+33)+(96*t+52)-2=160*t+83 := by omega
  have hy1 : (96*t+52-2)/2=48*t+25 := by omega
  rw [hx1,hy1]
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_pos hO1]
  have hx2 : ((160*t+83)+(48*t+25)-4)/2=104*t+52 := by omega
  have hy2 : ((160*t+83)+3*(48*t+25)-10)/4=76*t+37 := by omega
  rw [hx2,hy2]
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO2,dif_neg hS2,dif_neg hA2,dif_neg hE2]

private theorem full_forced_excluded_m0_j32_fifteen (t : Nat) :
    BB6.Agent3.fullForcedExcluded (64*t+33) (96*t+52)=true := by
  simp [BB6.Agent3.fullForcedExcluded,
    full_forced_normalize_m0_j32_fifteen]
  omega

/-- j=128t+71: even-affine, odd-low, and two six-even-right inverses. -/
private theorem full_forced_normalize_m0_j128_seventyone (t : Nat) :
    BB6.Agent3.fullForcedNormalize (256*t+145) (384*t+220) =
      (872*t+484,76*t+41) := by
  have hO0 : ¬ BB6.Agent3.oddLowGate (256*t+145) (384*t+220) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS0 : ¬ BB6.Agent3.evenSevenGate (256*t+145) (384*t+220) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA0 : BB6.Agent3.evenAffineGate (256*t+145) (384*t+220) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hO1 : BB6.Agent3.oddLowGate (640*t+363) (192*t+109) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS1 : ¬ BB6.Agent3.evenSevenGate (640*t+363) (192*t+109) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA1 : ¬ BB6.Agent3.evenAffineGate (640*t+363) (192*t+109) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE1 : ¬ BB6.Agent46.sixEvenRightGate (640*t+363) (192*t+109) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  have hO2 : ¬ BB6.Agent3.oddLowGate (416*t+234) (304*t+170) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS2 : ¬ BB6.Agent3.evenSevenGate (416*t+234) (304*t+170) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA2 : ¬ BB6.Agent3.evenAffineGate (416*t+234) (304*t+170) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE2 : BB6.Agent46.sixEvenRightGate (416*t+234) (304*t+170) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  have hO3 : ¬ BB6.Agent3.oddLowGate (720*t+402) (152*t+84) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS3 : ¬ BB6.Agent3.evenSevenGate (720*t+402) (152*t+84) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA3 : ¬ BB6.Agent3.evenAffineGate (720*t+402) (152*t+84) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE3 : BB6.Agent46.sixEvenRightGate (720*t+402) (152*t+84) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  have hO4 : ¬ BB6.Agent3.oddLowGate (872*t+484) (76*t+41) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS4 : ¬ BB6.Agent3.evenSevenGate (872*t+484) (76*t+41) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA4 : ¬ BB6.Agent3.evenAffineGate (872*t+484) (76*t+41) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE4 : ¬ BB6.Agent46.sixEvenRightGate (872*t+484) (76*t+41) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO0,dif_neg hS0,dif_pos hA0]
  have hx1 : (256*t+145)+(384*t+220)-2=640*t+363 := by omega
  have hy1 : (384*t+220-2)/2=192*t+109 := by omega
  rw [hx1,hy1]
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_pos hO1]
  have hx2 : ((640*t+363)+(192*t+109)-4)/2=416*t+234 := by omega
  have hy2 : ((640*t+363)+3*(192*t+109)-10)/4=304*t+170 := by omega
  rw [hx2,hy2]
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO2,dif_neg hS2,dif_neg hA2,dif_pos hE2]
  have hx3 : (416*t+234)+(304*t+170)-2=720*t+402 := by omega
  have hy3 : (304*t+170-2)/2=152*t+84 := by omega
  rw [hx3,hy3]
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO3,dif_neg hS3,dif_neg hA3,dif_pos hE3]
  have hx4 : (720*t+402)+(152*t+84)-2=872*t+484 := by omega
  have hy4 : (152*t+84-2)/2=76*t+41 := by omega
  rw [hx4,hy4]
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO4,dif_neg hS4,dif_neg hA4,dif_neg hE4]

private theorem full_forced_excluded_m0_j128_seventyone (t : Nat) :
    BB6.Agent3.fullForcedExcluded (256*t+145) (384*t+220)=true := by
  simp [BB6.Agent3.fullForcedExcluded,
    full_forced_normalize_m0_j128_seventyone]
  omega

/-- The j=32t+6 progression is a strict new exclusion. -/
theorem m0_j32_six_new_infinite_exclusion (t : Nat) :
    BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight (32*t+6) 0 ∧
    BB6.Agent3.fullForcedExcluded (64*t+15) (96*t+25)=true := by
  exact ⟨prior_high_allowed_m0_of_family (32*t+6) (Or.inl ⟨t,rfl⟩),
    full_forced_excluded_m0_j32_six t⟩

/-- The j=64t+58 progression is a strict new exclusion. -/
theorem m0_j64_fiftyeight_new_infinite_exclusion (t : Nat) :
    BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight (64*t+58) 0 ∧
    BB6.Agent3.fullForcedExcluded (128*t+119) (192*t+181)=true := by
  exact ⟨prior_high_allowed_m0_of_family (64*t+58) (Or.inr (Or.inl ⟨t,rfl⟩)),
    full_forced_excluded_m0_j64_fiftyeight t⟩

/-- The j=32t+21 progression is a strict new exclusion. -/
theorem m0_j32_twentyone_new_infinite_exclusion (t : Nat) :
    BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight (32*t+21) 0 ∧
    BB6.Agent3.fullForcedExcluded (64*t+45) (96*t+70)=true := by
  exact ⟨prior_high_allowed_m0_of_family (32*t+21)
      (Or.inr (Or.inr (Or.inl ⟨t,rfl⟩))),
    full_forced_excluded_m0_j32_twentyone t⟩

/-- The j=32t+15 progression is a strict new exclusion. -/
theorem m0_j32_fifteen_new_infinite_exclusion (t : Nat) :
    BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight (32*t+15) 0 ∧
    BB6.Agent3.fullForcedExcluded (64*t+33) (96*t+52)=true := by
  exact ⟨prior_high_allowed_m0_of_family (32*t+15)
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨t,rfl⟩)))),
    full_forced_excluded_m0_j32_fifteen t⟩

/-- The j=128t+71 progression is a strict new exclusion. -/
theorem m0_j128_seventyone_new_infinite_exclusion (t : Nat) :
    BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight (128*t+71) 0 ∧
    BB6.Agent3.fullForcedExcluded (256*t+145) (384*t+220)=true := by
  exact ⟨prior_high_allowed_m0_of_family (128*t+71)
      (Or.inr (Or.inr (Or.inr (Or.inr ⟨t,rfl⟩)))),
    full_forced_excluded_m0_j128_seventyone t⟩

/-- All five new families are absent from the authentic blank-tape orbit. -/
theorem m0_additional_families_blank_unreachable :
    (∀ t, ¬ BB6.Agent3.CReach (64*t+15) (96*t+25)) ∧
    (∀ t, ¬ BB6.Agent3.CReach (128*t+119) (192*t+181)) ∧
    (∀ t, ¬ BB6.Agent3.CReach (64*t+45) (96*t+70)) ∧
    (∀ t, ¬ BB6.Agent3.CReach (64*t+33) (96*t+52)) ∧
    (∀ t, ¬ BB6.Agent3.CReach (256*t+145) (384*t+220)) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro t h
    rcases h with ⟨time,hrun⟩
    exact (BB6.Agent3.fullForcedExcluded_sound
      (64*t+15) (96*t+25) (full_forced_excluded_m0_j32_six t) time) hrun
  · intro t h
    rcases h with ⟨time,hrun⟩
    exact (BB6.Agent3.fullForcedExcluded_sound
      (128*t+119) (192*t+181) (full_forced_excluded_m0_j64_fiftyeight t) time) hrun
  · intro t h
    rcases h with ⟨time,hrun⟩
    exact (BB6.Agent3.fullForcedExcluded_sound
      (64*t+45) (96*t+70) (full_forced_excluded_m0_j32_twentyone t) time) hrun
  · intro t h
    rcases h with ⟨time,hrun⟩
    exact (BB6.Agent3.fullForcedExcluded_sound
      (64*t+33) (96*t+52) (full_forced_excluded_m0_j32_fifteen t) time) hrun
  · intro t h
    rcases h with ⟨time,hrun⟩
    exact (BB6.Agent3.fullForcedExcluded_sound
      (256*t+145) (384*t+220) (full_forced_excluded_m0_j128_seventyone t) time) hrun

#print axioms prior_high_allowed_m0_of_family
#print axioms m0_j32_six_new_infinite_exclusion
#print axioms m0_j64_fiftyeight_new_infinite_exclusion
#print axioms m0_j32_twentyone_new_infinite_exclusion
#print axioms m0_j32_fifteen_new_infinite_exclusion
#print axioms m0_j128_seventyone_new_infinite_exclusion
#print axioms m0_additional_families_blank_unreachable

end BB6.Agent19M0Additional
