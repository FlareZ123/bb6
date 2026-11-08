import HighEvenRightC23FullForcedResidual
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent19M0Mod2048

private theorem prior_high_allowed_m0 (j : Nat)
    (hj4 : j%4 ≠ 0)
    (hright0 :
      (BB6.Agent15.affineNormalize (2*j+3) (3*j+7)).2 ≠ 4) :
    BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight j 0 := by
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

private theorem affine_right_no_step (x y : Nat)
    (hgate : ¬(4≤y ∧ y%2=0 ∧ (x+y)%4=1))
    (hy4 : y≠4) :
    (BB6.Agent15.affineNormalize x y).2 ≠ 4 := by
  unfold BB6.Agent15.affineNormalize
  rw [dif_neg hgate]
  exact hy4

private theorem affine_right_one_step (x y x' y' : Nat)
    (hgate : 4≤y ∧ y%2=0 ∧ (x+y)%4=1)
    (hx : x+y-2=x')
    (hy : (y-2)/2=y')
    (hnext : ¬(4≤y' ∧ y'%2=0 ∧ (x'+y')%4=1))
    (hy4 : y'≠4) :
    (BB6.Agent15.affineNormalize x y).2 ≠ 4 := by
  unfold BB6.Agent15.affineNormalize
  rw [dif_pos hgate,hx,hy]
  unfold BB6.Agent15.affineNormalize
  rw [dif_neg hnext]
  exact hy4

private theorem forced_step_odd {x y x' y' : Nat}
    (hO : BB6.Agent3.oddLowGate x y)
    (hx : (x+y-4)/2=x')
    (hy : (x+3*y-10)/4=y') :
    BB6.Agent3.fullForcedNormalize x y =
      BB6.Agent3.fullForcedNormalize x' y' := by
  conv =>
    lhs
    unfold BB6.Agent3.fullForcedNormalize
  rw [dif_pos hO,hx,hy]

private theorem forced_step_seven {x y x' y' : Nat}
    (hO : ¬BB6.Agent3.oddLowGate x y)
    (hS : BB6.Agent3.evenSevenGate x y)
    (hx : (x+y-5)/2=x')
    (hy : (x+3*y-9)/4=y') :
    BB6.Agent3.fullForcedNormalize x y =
      BB6.Agent3.fullForcedNormalize x' y' := by
  conv =>
    lhs
    unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO,dif_pos hS,hx,hy]

private theorem forced_step_affine {x y x' y' : Nat}
    (hO : ¬BB6.Agent3.oddLowGate x y)
    (hS : ¬BB6.Agent3.evenSevenGate x y)
    (hA : BB6.Agent3.evenAffineGate x y)
    (hx : x+y-2=x')
    (hy : (y-2)/2=y') :
    BB6.Agent3.fullForcedNormalize x y =
      BB6.Agent3.fullForcedNormalize x' y' := by
  conv =>
    lhs
    unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO,dif_neg hS,dif_pos hA,hx,hy]

private theorem forced_step_six {x y x' y' : Nat}
    (hO : ¬BB6.Agent3.oddLowGate x y)
    (hS : ¬BB6.Agent3.evenSevenGate x y)
    (hA : ¬BB6.Agent3.evenAffineGate x y)
    (hE : BB6.Agent46.sixEvenRightGate x y)
    (hx : x+y-2=x')
    (hy : (y-2)/2=y') :
    BB6.Agent3.fullForcedNormalize x y =
      BB6.Agent3.fullForcedNormalize x' y' := by
  conv =>
    lhs
    unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO,dif_neg hS,dif_neg hA,dif_pos hE,hx,hy]

private theorem forced_terminal {x y : Nat}
    (hO : ¬BB6.Agent3.oddLowGate x y)
    (hS : ¬BB6.Agent3.evenSevenGate x y)
    (hA : ¬BB6.Agent3.evenAffineGate x y)
    (hE : ¬BB6.Agent46.sixEvenRightGate x y) :
    BB6.Agent3.fullForcedNormalize x y = (x,y) := by
  conv =>
    lhs
    unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO,dif_neg hS,dif_neg hA,dif_neg hE]

/- Family j = 2048*t + 534. The forced path is O, E, S, O, E, E. -/
private theorem normalize_m0_2048_534 (t : Nat) :
    BB6.Agent3.fullForcedNormalize (4096*t+1071) (6144*t+1609) =
      (13736*t+3570,1324*t+343) := by
  have hO0 : BB6.Agent3.oddLowGate (4096*t+1071) (6144*t+1609) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hO1 : ¬BB6.Agent3.oddLowGate (5120*t+1338) (5632*t+1472) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS1 : ¬BB6.Agent3.evenSevenGate (5120*t+1338) (5632*t+1472) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA1 : ¬BB6.Agent3.evenAffineGate (5120*t+1338) (5632*t+1472) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE1 : BB6.Agent46.sixEvenRightGate (5120*t+1338) (5632*t+1472) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  have hO2 : ¬BB6.Agent3.oddLowGate (10752*t+2808) (2816*t+735) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS2 : BB6.Agent3.evenSevenGate (10752*t+2808) (2816*t+735) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hO3 : BB6.Agent3.oddLowGate (6784*t+1769) (4800*t+1251) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hO4 : ¬BB6.Agent3.oddLowGate (5792*t+1508) (5296*t+1378) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS4 : ¬BB6.Agent3.evenSevenGate (5792*t+1508) (5296*t+1378) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA4 : ¬BB6.Agent3.evenAffineGate (5792*t+1508) (5296*t+1378) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE4 : BB6.Agent46.sixEvenRightGate (5792*t+1508) (5296*t+1378) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  have hO5 : ¬BB6.Agent3.oddLowGate (11088*t+2884) (2648*t+688) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS5 : ¬BB6.Agent3.evenSevenGate (11088*t+2884) (2648*t+688) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA5 : ¬BB6.Agent3.evenAffineGate (11088*t+2884) (2648*t+688) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE5 : BB6.Agent46.sixEvenRightGate (11088*t+2884) (2648*t+688) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  have hO6 : ¬BB6.Agent3.oddLowGate (13736*t+3570) (1324*t+343) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS6 : ¬BB6.Agent3.evenSevenGate (13736*t+3570) (1324*t+343) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA6 : ¬BB6.Agent3.evenAffineGate (13736*t+3570) (1324*t+343) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE6 : ¬BB6.Agent46.sixEvenRightGate (13736*t+3570) (1324*t+343) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  calc
    BB6.Agent3.fullForcedNormalize (4096*t+1071) (6144*t+1609) =
        BB6.Agent3.fullForcedNormalize (5120*t+1338) (5632*t+1472) :=
      forced_step_odd hO0 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (10752*t+2808) (2816*t+735) :=
      forced_step_six hO1 hS1 hA1 hE1 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (6784*t+1769) (4800*t+1251) :=
      forced_step_seven hO2 hS2 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (5792*t+1508) (5296*t+1378) :=
      forced_step_odd hO3 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (11088*t+2884) (2648*t+688) :=
      forced_step_six hO4 hS4 hA4 hE4 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (13736*t+3570) (1324*t+343) :=
      forced_step_six hO5 hS5 hA5 hE5 (by omega) (by omega)
    _ = (13736*t+3570,1324*t+343) :=
      forced_terminal hO6 hS6 hA6 hE6

/- Family j = 2048*t + 581. The forced path is E, E, A, O, S, O. -/
private theorem normalize_m0_2048_581 (t : Nat) :
    BB6.Agent3.fullForcedNormalize (4096*t+1165) (6144*t+1750) =
      (5608*t+1586,5388*t+1523) := by
  have hO0 : ¬BB6.Agent3.oddLowGate (4096*t+1165) (6144*t+1750) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS0 : ¬BB6.Agent3.evenSevenGate (4096*t+1165) (6144*t+1750) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA0 : ¬BB6.Agent3.evenAffineGate (4096*t+1165) (6144*t+1750) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE0 : BB6.Agent46.sixEvenRightGate (4096*t+1165) (6144*t+1750) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  have hO1 : ¬BB6.Agent3.oddLowGate (10240*t+2913) (3072*t+874) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS1 : ¬BB6.Agent3.evenSevenGate (10240*t+2913) (3072*t+874) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA1 : ¬BB6.Agent3.evenAffineGate (10240*t+2913) (3072*t+874) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE1 : BB6.Agent46.sixEvenRightGate (10240*t+2913) (3072*t+874) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  have hO2 : ¬BB6.Agent3.oddLowGate (13312*t+3785) (1536*t+436) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS2 : ¬BB6.Agent3.evenSevenGate (13312*t+3785) (1536*t+436) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA2 : BB6.Agent3.evenAffineGate (13312*t+3785) (1536*t+436) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hO3 : BB6.Agent3.oddLowGate (14848*t+4219) (768*t+217) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hO4 : ¬BB6.Agent3.oddLowGate (7808*t+2216) (4288*t+1215) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS4 : BB6.Agent3.evenSevenGate (7808*t+2216) (4288*t+1215) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hO5 : BB6.Agent3.oddLowGate (6048*t+1713) (5168*t+1463) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hO6 : ¬BB6.Agent3.oddLowGate (5608*t+1586) (5388*t+1523) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS6 : ¬BB6.Agent3.evenSevenGate (5608*t+1586) (5388*t+1523) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA6 : ¬BB6.Agent3.evenAffineGate (5608*t+1586) (5388*t+1523) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE6 : ¬BB6.Agent46.sixEvenRightGate (5608*t+1586) (5388*t+1523) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  calc
    BB6.Agent3.fullForcedNormalize (4096*t+1165) (6144*t+1750) =
        BB6.Agent3.fullForcedNormalize (10240*t+2913) (3072*t+874) :=
      forced_step_six hO0 hS0 hA0 hE0 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (13312*t+3785) (1536*t+436) :=
      forced_step_six hO1 hS1 hA1 hE1 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (14848*t+4219) (768*t+217) :=
      forced_step_affine hO2 hS2 hA2 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (7808*t+2216) (4288*t+1215) :=
      forced_step_odd hO3 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (6048*t+1713) (5168*t+1463) :=
      forced_step_seven hO4 hS4 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (5608*t+1586) (5388*t+1523) :=
      forced_step_odd hO5 (by omega) (by omega)
    _ = (5608*t+1586,5388*t+1523) :=
      forced_terminal hO6 hS6 hA6 hE6

/- Family j = 2048*t + 1159. The forced path is A, O, E, E, S, O. -/
private theorem normalize_m0_2048_1159 (t : Nat) :
    BB6.Agent3.fullForcedNormalize (4096*t+2321) (6144*t+3484) =
      (5992*t+3386,5196*t+2935) := by
  have hO0 : ¬BB6.Agent3.oddLowGate (4096*t+2321) (6144*t+3484) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS0 : ¬BB6.Agent3.evenSevenGate (4096*t+2321) (6144*t+3484) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA0 : BB6.Agent3.evenAffineGate (4096*t+2321) (6144*t+3484) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hO1 : BB6.Agent3.oddLowGate (10240*t+5803) (3072*t+1741) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hO2 : ¬BB6.Agent3.oddLowGate (6656*t+3770) (4864*t+2754) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS2 : ¬BB6.Agent3.evenSevenGate (6656*t+3770) (4864*t+2754) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA2 : ¬BB6.Agent3.evenAffineGate (6656*t+3770) (4864*t+2754) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE2 : BB6.Agent46.sixEvenRightGate (6656*t+3770) (4864*t+2754) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  have hO3 : ¬BB6.Agent3.oddLowGate (11520*t+6522) (2432*t+1376) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS3 : ¬BB6.Agent3.evenSevenGate (11520*t+6522) (2432*t+1376) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA3 : ¬BB6.Agent3.evenAffineGate (11520*t+6522) (2432*t+1376) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE3 : BB6.Agent46.sixEvenRightGate (11520*t+6522) (2432*t+1376) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  have hO4 : ¬BB6.Agent3.oddLowGate (13952*t+7896) (1216*t+687) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS4 : BB6.Agent3.evenSevenGate (13952*t+7896) (1216*t+687) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hO5 : BB6.Agent3.oddLowGate (7584*t+4289) (4400*t+2487) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hO6 : ¬BB6.Agent3.oddLowGate (5992*t+3386) (5196*t+2935) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS6 : ¬BB6.Agent3.evenSevenGate (5992*t+3386) (5196*t+2935) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA6 : ¬BB6.Agent3.evenAffineGate (5992*t+3386) (5196*t+2935) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE6 : ¬BB6.Agent46.sixEvenRightGate (5992*t+3386) (5196*t+2935) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  calc
    BB6.Agent3.fullForcedNormalize (4096*t+2321) (6144*t+3484) =
        BB6.Agent3.fullForcedNormalize (10240*t+5803) (3072*t+1741) :=
      forced_step_affine hO0 hS0 hA0 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (6656*t+3770) (4864*t+2754) :=
      forced_step_odd hO1 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (11520*t+6522) (2432*t+1376) :=
      forced_step_six hO2 hS2 hA2 hE2 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (13952*t+7896) (1216*t+687) :=
      forced_step_six hO3 hS3 hA3 hE3 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (7584*t+4289) (4400*t+2487) :=
      forced_step_seven hO4 hS4 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (5992*t+3386) (5196*t+2935) :=
      forced_step_odd hO5 (by omega) (by omega)
    _ = (5992*t+3386,5196*t+2935) :=
      forced_terminal hO6 hS6 hA6 hE6

/- Family j = 2048*t + 1343. The forced path is A, O, S, O, E, E. -/
private theorem normalize_m0_2048_1343 (t : Nat) :
    BB6.Agent3.fullForcedNormalize (4096*t+2689) (6144*t+4036) =
      (13672*t+8954,1356*t+887) := by
  have hO0 : ¬BB6.Agent3.oddLowGate (4096*t+2689) (6144*t+4036) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS0 : ¬BB6.Agent3.evenSevenGate (4096*t+2689) (6144*t+4036) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA0 : BB6.Agent3.evenAffineGate (4096*t+2689) (6144*t+4036) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hO1 : BB6.Agent3.oddLowGate (10240*t+6723) (3072*t+2017) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hO2 : ¬BB6.Agent3.oddLowGate (6656*t+4368) (4864*t+3191) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS2 : BB6.Agent3.evenSevenGate (6656*t+4368) (4864*t+3191) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hO3 : BB6.Agent3.oddLowGate (5760*t+3777) (5312*t+3483) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hO4 : ¬BB6.Agent3.oddLowGate (5536*t+3628) (5424*t+3554) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS4 : ¬BB6.Agent3.evenSevenGate (5536*t+3628) (5424*t+3554) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA4 : ¬BB6.Agent3.evenAffineGate (5536*t+3628) (5424*t+3554) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE4 : BB6.Agent46.sixEvenRightGate (5536*t+3628) (5424*t+3554) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  have hO5 : ¬BB6.Agent3.oddLowGate (10960*t+7180) (2712*t+1776) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS5 : ¬BB6.Agent3.evenSevenGate (10960*t+7180) (2712*t+1776) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA5 : ¬BB6.Agent3.evenAffineGate (10960*t+7180) (2712*t+1776) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE5 : BB6.Agent46.sixEvenRightGate (10960*t+7180) (2712*t+1776) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  have hO6 : ¬BB6.Agent3.oddLowGate (13672*t+8954) (1356*t+887) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS6 : ¬BB6.Agent3.evenSevenGate (13672*t+8954) (1356*t+887) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA6 : ¬BB6.Agent3.evenAffineGate (13672*t+8954) (1356*t+887) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE6 : ¬BB6.Agent46.sixEvenRightGate (13672*t+8954) (1356*t+887) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  calc
    BB6.Agent3.fullForcedNormalize (4096*t+2689) (6144*t+4036) =
        BB6.Agent3.fullForcedNormalize (10240*t+6723) (3072*t+2017) :=
      forced_step_affine hO0 hS0 hA0 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (6656*t+4368) (4864*t+3191) :=
      forced_step_odd hO1 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (5760*t+3777) (5312*t+3483) :=
      forced_step_seven hO2 hS2 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (5536*t+3628) (5424*t+3554) :=
      forced_step_odd hO3 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (10960*t+7180) (2712*t+1776) :=
      forced_step_six hO4 hS4 hA4 hE4 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (13672*t+8954) (1356*t+887) :=
      forced_step_six hO5 hS5 hA5 hE5 (by omega) (by omega)
    _ = (13672*t+8954,1356*t+887) :=
      forced_terminal hO6 hS6 hA6 hE6

private theorem excluded_m0_2048_534 (t : Nat) :
    BB6.Agent3.fullForcedExcluded (4096*t+1071) (6144*t+1609)=true := by
  simp [BB6.Agent3.fullForcedExcluded,normalize_m0_2048_534]
  omega

private theorem excluded_m0_2048_581 (t : Nat) :
    BB6.Agent3.fullForcedExcluded (4096*t+1165) (6144*t+1750)=true := by
  simp [BB6.Agent3.fullForcedExcluded,normalize_m0_2048_581]
  omega

private theorem excluded_m0_2048_1159 (t : Nat) :
    BB6.Agent3.fullForcedExcluded (4096*t+2321) (6144*t+3484)=true := by
  simp [BB6.Agent3.fullForcedExcluded,normalize_m0_2048_1159]
  omega

private theorem excluded_m0_2048_1343 (t : Nat) :
    BB6.Agent3.fullForcedExcluded (4096*t+2689) (6144*t+4036)=true := by
  simp [BB6.Agent3.fullForcedExcluded,normalize_m0_2048_1343]
  omega

private theorem affine_right_m0_2048_534 (t : Nat) :
    (BB6.Agent15.affineNormalize (4096*t+1071) (6144*t+1609)).2≠4 := by
  apply affine_right_no_step
  · omega
  · omega

private theorem affine_right_m0_2048_581 (t : Nat) :
    (BB6.Agent15.affineNormalize (4096*t+1165) (6144*t+1750)).2≠4 := by
  apply affine_right_no_step
  · omega
  · omega

private theorem affine_right_m0_2048_1159 (t : Nat) :
    (BB6.Agent15.affineNormalize (4096*t+2321) (6144*t+3484)).2≠4 := by
  apply affine_right_one_step (4096*t+2321) (6144*t+3484)
    (10240*t+5803) (3072*t+1741)
  · omega
  · omega
  · omega
  · omega

private theorem affine_right_m0_2048_1343 (t : Nat) :
    (BB6.Agent15.affineNormalize (4096*t+2689) (6144*t+4036)).2≠4 := by
  apply affine_right_one_step (4096*t+2689) (6144*t+4036)
    (10240*t+6723) (3072*t+2017)
  · omega
  · omega
  · omega
  · omega

theorem m0_2048_534_admitted_and_excluded (t : Nat) :
    BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight
        (2048*t+534) 0 ∧
      BB6.Agent3.fullForcedExcluded (4096*t+1071)
        (6144*t+1609)=true := by
  constructor
  · apply prior_high_allowed_m0
    · omega
    · simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        affine_right_m0_2048_534 t
  · exact excluded_m0_2048_534 t

theorem m0_2048_581_admitted_and_excluded (t : Nat) :
    BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight
        (2048*t+581) 0 ∧
      BB6.Agent3.fullForcedExcluded (4096*t+1165)
        (6144*t+1750)=true := by
  constructor
  · apply prior_high_allowed_m0
    · omega
    · simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        affine_right_m0_2048_581 t
  · exact excluded_m0_2048_581 t

theorem m0_2048_1159_admitted_and_excluded (t : Nat) :
    BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight
        (2048*t+1159) 0 ∧
      BB6.Agent3.fullForcedExcluded (4096*t+2321)
        (6144*t+3484)=true := by
  constructor
  · apply prior_high_allowed_m0
    · omega
    · simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        affine_right_m0_2048_1159 t
  · exact excluded_m0_2048_1159 t

theorem m0_2048_1343_admitted_and_excluded (t : Nat) :
    BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight
        (2048*t+1343) 0 ∧
      BB6.Agent3.fullForcedExcluded (4096*t+2689)
        (6144*t+4036)=true := by
  constructor
  · apply prior_high_allowed_m0
    · omega
    · simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        affine_right_m0_2048_1343 t
  · exact excluded_m0_2048_1343 t

theorem m0_2048_534_blank_unreachable (t : Nat) :
    ¬ BB6.Agent3.CReach (4096*t+1071) (6144*t+1609) := by
  intro h
  rcases h with ⟨time,hr⟩
  exact (BB6.Agent3.fullForcedExcluded_sound _ _
    (excluded_m0_2048_534 t) time) hr

theorem m0_2048_581_blank_unreachable (t : Nat) :
    ¬ BB6.Agent3.CReach (4096*t+1165) (6144*t+1750) := by
  intro h
  rcases h with ⟨time,hr⟩
  exact (BB6.Agent3.fullForcedExcluded_sound _ _
    (excluded_m0_2048_581 t) time) hr

theorem m0_2048_1159_blank_unreachable (t : Nat) :
    ¬ BB6.Agent3.CReach (4096*t+2321) (6144*t+3484) := by
  intro h
  rcases h with ⟨time,hr⟩
  exact (BB6.Agent3.fullForcedExcluded_sound _ _
    (excluded_m0_2048_1159 t) time) hr

theorem m0_2048_1343_blank_unreachable (t : Nat) :
    ¬ BB6.Agent3.CReach (4096*t+2689) (6144*t+4036) := by
  intro h
  rcases h with ⟨time,hr⟩
  exact (BB6.Agent3.fullForcedExcluded_sound _ _
    (excluded_m0_2048_1343 t) time) hr

#print axioms prior_high_allowed_m0
#print axioms m0_2048_534_admitted_and_excluded
#print axioms m0_2048_581_admitted_and_excluded
#print axioms m0_2048_1159_admitted_and_excluded
#print axioms m0_2048_1343_admitted_and_excluded
#print axioms m0_2048_534_blank_unreachable
#print axioms m0_2048_581_blank_unreachable
#print axioms m0_2048_1159_blank_unreachable
#print axioms m0_2048_1343_blank_unreachable


/- Two further 8192-stride subfamilies of the six finite residual m=0
   candidates. Their terminal odd-right states have sum 1 mod 4. -/

private theorem normalize_m0_8192_1046 (s : Nat) :
    BB6.Agent3.fullForcedNormalize (16384*s+2095) (24576*s+3145) =
      (62888*s+8010,1324*s+167) := by
  have hO0 : BB6.Agent3.oddLowGate (16384*s+2095) (24576*s+3145) := by
    unfold BB6.Agent3.oddLowGate; omega
  have hO1 : ¬BB6.Agent3.oddLowGate (20480*s+2618) (22528*s+2880) := by
    unfold BB6.Agent3.oddLowGate; omega
  have hS1 : ¬BB6.Agent3.evenSevenGate (20480*s+2618) (22528*s+2880) := by
    unfold BB6.Agent3.evenSevenGate; omega
  have hA1 : ¬BB6.Agent3.evenAffineGate (20480*s+2618) (22528*s+2880) := by
    unfold BB6.Agent3.evenAffineGate; omega
  have hE1 : BB6.Agent46.sixEvenRightGate (20480*s+2618) (22528*s+2880) := by
    unfold BB6.Agent46.sixEvenRightGate; omega
  have hO2 : ¬BB6.Agent3.oddLowGate (43008*s+5496) (11264*s+1439) := by
    unfold BB6.Agent3.oddLowGate; omega
  have hS2 : BB6.Agent3.evenSevenGate (43008*s+5496) (11264*s+1439) := by
    unfold BB6.Agent3.evenSevenGate; omega
  have hO3 : BB6.Agent3.oddLowGate (27136*s+3465) (19200*s+2451) := by
    unfold BB6.Agent3.oddLowGate; omega
  have hO4 : ¬BB6.Agent3.oddLowGate (23168*s+2956) (21184*s+2702) := by
    unfold BB6.Agent3.oddLowGate; omega
  have hS4 : ¬BB6.Agent3.evenSevenGate (23168*s+2956) (21184*s+2702) := by
    unfold BB6.Agent3.evenSevenGate; omega
  have hA4 : ¬BB6.Agent3.evenAffineGate (23168*s+2956) (21184*s+2702) := by
    unfold BB6.Agent3.evenAffineGate; omega
  have hE4 : BB6.Agent46.sixEvenRightGate (23168*s+2956) (21184*s+2702) := by
    unfold BB6.Agent46.sixEvenRightGate; omega
  have hO5 : ¬BB6.Agent3.oddLowGate (44352*s+5656) (10592*s+1350) := by
    unfold BB6.Agent3.oddLowGate; omega
  have hS5 : ¬BB6.Agent3.evenSevenGate (44352*s+5656) (10592*s+1350) := by
    unfold BB6.Agent3.evenSevenGate; omega
  have hA5 : ¬BB6.Agent3.evenAffineGate (44352*s+5656) (10592*s+1350) := by
    unfold BB6.Agent3.evenAffineGate; omega
  have hE5 : BB6.Agent46.sixEvenRightGate (44352*s+5656) (10592*s+1350) := by
    unfold BB6.Agent46.sixEvenRightGate; omega
  have hO6 : ¬BB6.Agent3.oddLowGate (54944*s+7004) (5296*s+674) := by
    unfold BB6.Agent3.oddLowGate; omega
  have hS6 : ¬BB6.Agent3.evenSevenGate (54944*s+7004) (5296*s+674) := by
    unfold BB6.Agent3.evenSevenGate; omega
  have hA6 : ¬BB6.Agent3.evenAffineGate (54944*s+7004) (5296*s+674) := by
    unfold BB6.Agent3.evenAffineGate; omega
  have hE6 : BB6.Agent46.sixEvenRightGate (54944*s+7004) (5296*s+674) := by
    unfold BB6.Agent46.sixEvenRightGate; omega
  have hO7 : ¬BB6.Agent3.oddLowGate (60240*s+7676) (2648*s+336) := by
    unfold BB6.Agent3.oddLowGate; omega
  have hS7 : ¬BB6.Agent3.evenSevenGate (60240*s+7676) (2648*s+336) := by
    unfold BB6.Agent3.evenSevenGate; omega
  have hA7 : ¬BB6.Agent3.evenAffineGate (60240*s+7676) (2648*s+336) := by
    unfold BB6.Agent3.evenAffineGate; omega
  have hE7 : BB6.Agent46.sixEvenRightGate (60240*s+7676) (2648*s+336) := by
    unfold BB6.Agent46.sixEvenRightGate; omega
  have hO8 : ¬BB6.Agent3.oddLowGate (62888*s+8010) (1324*s+167) := by
    unfold BB6.Agent3.oddLowGate; omega
  have hS8 : ¬BB6.Agent3.evenSevenGate (62888*s+8010) (1324*s+167) := by
    unfold BB6.Agent3.evenSevenGate; omega
  have hA8 : ¬BB6.Agent3.evenAffineGate (62888*s+8010) (1324*s+167) := by
    unfold BB6.Agent3.evenAffineGate; omega
  have hE8 : ¬BB6.Agent46.sixEvenRightGate (62888*s+8010) (1324*s+167) := by
    unfold BB6.Agent46.sixEvenRightGate; omega
  calc
    BB6.Agent3.fullForcedNormalize (16384*s+2095) (24576*s+3145) =
        BB6.Agent3.fullForcedNormalize (20480*s+2618) (22528*s+2880) :=
      forced_step_odd hO0 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (43008*s+5496) (11264*s+1439) :=
      forced_step_six hO1 hS1 hA1 hE1 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (27136*s+3465) (19200*s+2451) :=
      forced_step_seven hO2 hS2 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (23168*s+2956) (21184*s+2702) :=
      forced_step_odd hO3 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (44352*s+5656) (10592*s+1350) :=
      forced_step_six hO4 hS4 hA4 hE4 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (54944*s+7004) (5296*s+674) :=
      forced_step_six hO5 hS5 hA5 hE5 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (60240*s+7676) (2648*s+336) :=
      forced_step_six hO6 hS6 hA6 hE6 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (62888*s+8010) (1324*s+167) :=
      forced_step_six hO7 hS7 hA7 hE7 (by omega) (by omega)
    _ = (62888*s+8010,1324*s+167) :=
      forced_terminal hO8 hS8 hA8 hE8

private theorem normalize_m0_8192_3141 (s : Nat) :
    BB6.Agent3.fullForcedNormalize (16384*s+6285) (24576*s+9430) =
      (54760*s+20978,5388*s+2063) := by
  have hO0 : ¬BB6.Agent3.oddLowGate (16384*s+6285) (24576*s+9430) := by
    unfold BB6.Agent3.oddLowGate; omega
  have hS0 : ¬BB6.Agent3.evenSevenGate (16384*s+6285) (24576*s+9430) := by
    unfold BB6.Agent3.evenSevenGate; omega
  have hA0 : ¬BB6.Agent3.evenAffineGate (16384*s+6285) (24576*s+9430) := by
    unfold BB6.Agent3.evenAffineGate; omega
  have hE0 : BB6.Agent46.sixEvenRightGate (16384*s+6285) (24576*s+9430) := by
    unfold BB6.Agent46.sixEvenRightGate; omega
  have hO1 : ¬BB6.Agent3.oddLowGate (40960*s+15713) (12288*s+4714) := by
    unfold BB6.Agent3.oddLowGate; omega
  have hS1 : ¬BB6.Agent3.evenSevenGate (40960*s+15713) (12288*s+4714) := by
    unfold BB6.Agent3.evenSevenGate; omega
  have hA1 : ¬BB6.Agent3.evenAffineGate (40960*s+15713) (12288*s+4714) := by
    unfold BB6.Agent3.evenAffineGate; omega
  have hE1 : BB6.Agent46.sixEvenRightGate (40960*s+15713) (12288*s+4714) := by
    unfold BB6.Agent46.sixEvenRightGate; omega
  have hO2 : ¬BB6.Agent3.oddLowGate (53248*s+20425) (6144*s+2356) := by
    unfold BB6.Agent3.oddLowGate; omega
  have hS2 : ¬BB6.Agent3.evenSevenGate (53248*s+20425) (6144*s+2356) := by
    unfold BB6.Agent3.evenSevenGate; omega
  have hA2 : BB6.Agent3.evenAffineGate (53248*s+20425) (6144*s+2356) := by
    unfold BB6.Agent3.evenAffineGate; omega
  have hO3 : BB6.Agent3.oddLowGate (59392*s+22779) (3072*s+1177) := by
    unfold BB6.Agent3.oddLowGate; omega
  have hO4 : ¬BB6.Agent3.oddLowGate (31232*s+11976) (17152*s+6575) := by
    unfold BB6.Agent3.oddLowGate; omega
  have hS4 : BB6.Agent3.evenSevenGate (31232*s+11976) (17152*s+6575) := by
    unfold BB6.Agent3.evenSevenGate; omega
  have hO5 : BB6.Agent3.oddLowGate (24192*s+9273) (20672*s+7923) := by
    unfold BB6.Agent3.oddLowGate; omega
  have hO6 : ¬BB6.Agent3.oddLowGate (22432*s+8596) (21552*s+8258) := by
    unfold BB6.Agent3.oddLowGate; omega
  have hS6 : ¬BB6.Agent3.evenSevenGate (22432*s+8596) (21552*s+8258) := by
    unfold BB6.Agent3.evenSevenGate; omega
  have hA6 : ¬BB6.Agent3.evenAffineGate (22432*s+8596) (21552*s+8258) := by
    unfold BB6.Agent3.evenAffineGate; omega
  have hE6 : BB6.Agent46.sixEvenRightGate (22432*s+8596) (21552*s+8258) := by
    unfold BB6.Agent46.sixEvenRightGate; omega
  have hO7 : ¬BB6.Agent3.oddLowGate (43984*s+16852) (10776*s+4128) := by
    unfold BB6.Agent3.oddLowGate; omega
  have hS7 : ¬BB6.Agent3.evenSevenGate (43984*s+16852) (10776*s+4128) := by
    unfold BB6.Agent3.evenSevenGate; omega
  have hA7 : ¬BB6.Agent3.evenAffineGate (43984*s+16852) (10776*s+4128) := by
    unfold BB6.Agent3.evenAffineGate; omega
  have hE7 : BB6.Agent46.sixEvenRightGate (43984*s+16852) (10776*s+4128) := by
    unfold BB6.Agent46.sixEvenRightGate; omega
  have hO8 : ¬BB6.Agent3.oddLowGate (54760*s+20978) (5388*s+2063) := by
    unfold BB6.Agent3.oddLowGate; omega
  have hS8 : ¬BB6.Agent3.evenSevenGate (54760*s+20978) (5388*s+2063) := by
    unfold BB6.Agent3.evenSevenGate; omega
  have hA8 : ¬BB6.Agent3.evenAffineGate (54760*s+20978) (5388*s+2063) := by
    unfold BB6.Agent3.evenAffineGate; omega
  have hE8 : ¬BB6.Agent46.sixEvenRightGate (54760*s+20978) (5388*s+2063) := by
    unfold BB6.Agent46.sixEvenRightGate; omega
  calc
    BB6.Agent3.fullForcedNormalize (16384*s+6285) (24576*s+9430) =
        BB6.Agent3.fullForcedNormalize (40960*s+15713) (12288*s+4714) :=
      forced_step_six hO0 hS0 hA0 hE0 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (53248*s+20425) (6144*s+2356) :=
      forced_step_six hO1 hS1 hA1 hE1 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (59392*s+22779) (3072*s+1177) :=
      forced_step_affine hO2 hS2 hA2 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (31232*s+11976) (17152*s+6575) :=
      forced_step_odd hO3 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (24192*s+9273) (20672*s+7923) :=
      forced_step_seven hO4 hS4 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (22432*s+8596) (21552*s+8258) :=
      forced_step_odd hO5 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (43984*s+16852) (10776*s+4128) :=
      forced_step_six hO6 hS6 hA6 hE6 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (54760*s+20978) (5388*s+2063) :=
      forced_step_six hO7 hS7 hA7 hE7 (by omega) (by omega)
    _ = (54760*s+20978,5388*s+2063) :=
      forced_terminal hO8 hS8 hA8 hE8

private theorem excluded_m0_8192_1046 (s : Nat) :
    BB6.Agent3.fullForcedExcluded (16384*s+2095) (24576*s+3145)=true := by
  simp [BB6.Agent3.fullForcedExcluded,normalize_m0_8192_1046]
  omega

private theorem excluded_m0_8192_3141 (s : Nat) :
    BB6.Agent3.fullForcedExcluded (16384*s+6285) (24576*s+9430)=true := by
  simp [BB6.Agent3.fullForcedExcluded,normalize_m0_8192_3141]
  omega

private theorem affine_right_m0_8192_1046 (s : Nat) :
    (BB6.Agent15.affineNormalize (16384*s+2095)
      (24576*s+3145)).2 ≠ 4 := by
  apply affine_right_no_step <;> omega

private theorem affine_right_m0_8192_3141 (s : Nat) :
    (BB6.Agent15.affineNormalize (16384*s+6285)
      (24576*s+9430)).2 ≠ 4 := by
  apply affine_right_no_step <;> omega

theorem m0_8192_1046_admitted_and_excluded (s : Nat) :
    BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight
        (8192*s+1046) 0 ∧
      BB6.Agent3.fullForcedExcluded (16384*s+2095)
        (24576*s+3145)=true := by
  constructor
  · apply prior_high_allowed_m0
    · omega
    · have hx : 2*(8192*s+1046)+3=16384*s+2095 := by omega
      have hy : 3*(8192*s+1046)+7=24576*s+3145 := by omega
      rw [hx,hy]
      exact affine_right_m0_8192_1046 s
  · exact excluded_m0_8192_1046 s

theorem m0_8192_3141_admitted_and_excluded (s : Nat) :
    BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight
        (8192*s+3141) 0 ∧
      BB6.Agent3.fullForcedExcluded (16384*s+6285)
        (24576*s+9430)=true := by
  constructor
  · apply prior_high_allowed_m0
    · omega
    · have hx : 2*(8192*s+3141)+3=16384*s+6285 := by omega
      have hy : 3*(8192*s+3141)+7=24576*s+9430 := by omega
      rw [hx,hy]
      exact affine_right_m0_8192_3141 s
  · exact excluded_m0_8192_3141 s

theorem m0_8192_1046_blank_unreachable (s : Nat) :
    ¬ BB6.Agent3.CReach (16384*s+2095) (24576*s+3145) := by
  intro h
  rcases h with ⟨time,hrun⟩
  exact (BB6.Agent3.fullForcedExcluded_sound _ _
    (excluded_m0_8192_1046 s) time) hrun

theorem m0_8192_3141_blank_unreachable (s : Nat) :
    ¬ BB6.Agent3.CReach (16384*s+6285) (24576*s+9430) := by
  intro h
  rcases h with ⟨time,hrun⟩
  exact (BB6.Agent3.fullForcedExcluded_sound _ _
    (excluded_m0_8192_3141 s) time) hrun

theorem m0_8192_1046_new_bool_filter (s : Nat) :
    BB6.Agent3FullForcedResidual.highAllowedC23WithEvenRightFullForcedBool
      (8192*s+1046) 0 = false := by
  have hprior :
      BB6.Agent3FullForcedResidual.highAllowedC23WithEvenRightBool
        (8192*s+1046) 0 = true :=
    (BB6.Agent3FullForcedResidual.highAllowedC23WithEvenRightBool_iff
      (8192*s+1046) 0).mpr
        (m0_8192_1046_admitted_and_excluded s).1
  have hx :
      BB6.Agent3FullForcedResidual.highTargetX (8192*s+1046)
        =16384*s+2095 := by
    simp [BB6.Agent3FullForcedResidual.highTargetX]
    omega
  have hy :
      BB6.Agent3FullForcedResidual.highTargetY (8192*s+1046) 0
        =24576*s+3145 := by
    simp [BB6.Agent3FullForcedResidual.highTargetY]
    omega
  have hforced :
      BB6.Agent3.fullForcedExcluded
        (BB6.Agent3FullForcedResidual.highTargetX (8192*s+1046))
        (BB6.Agent3FullForcedResidual.highTargetY (8192*s+1046) 0)=true := by
    rw [hx,hy]
    exact (m0_8192_1046_admitted_and_excluded s).2
  simp [BB6.Agent3FullForcedResidual.highAllowedC23WithEvenRightFullForcedBool,
    hprior,hforced]

theorem m0_8192_3141_new_bool_filter (s : Nat) :
    BB6.Agent3FullForcedResidual.highAllowedC23WithEvenRightFullForcedBool
      (8192*s+3141) 0 = false := by
  have hprior :
      BB6.Agent3FullForcedResidual.highAllowedC23WithEvenRightBool
        (8192*s+3141) 0 = true :=
    (BB6.Agent3FullForcedResidual.highAllowedC23WithEvenRightBool_iff
      (8192*s+3141) 0).mpr
        (m0_8192_3141_admitted_and_excluded s).1
  have hx :
      BB6.Agent3FullForcedResidual.highTargetX (8192*s+3141)
        =16384*s+6285 := by
    simp [BB6.Agent3FullForcedResidual.highTargetX]
    omega
  have hy :
      BB6.Agent3FullForcedResidual.highTargetY (8192*s+3141) 0
        =24576*s+9430 := by
    simp [BB6.Agent3FullForcedResidual.highTargetY]
    omega
  have hforced :
      BB6.Agent3.fullForcedExcluded
        (BB6.Agent3FullForcedResidual.highTargetX (8192*s+3141))
        (BB6.Agent3FullForcedResidual.highTargetY (8192*s+3141) 0)=true := by
    rw [hx,hy]
    exact (m0_8192_3141_admitted_and_excluded s).2
  simp [BB6.Agent3FullForcedResidual.highAllowedC23WithEvenRightFullForcedBool,
    hprior,hforced]

#print axioms m0_8192_1046_admitted_and_excluded
#print axioms m0_8192_3141_admitted_and_excluded
#print axioms m0_8192_1046_blank_unreachable
#print axioms m0_8192_3141_blank_unreachable
#print axioms m0_8192_1046_new_bool_filter
#print axioms m0_8192_3141_new_bool_filter


end BB6.Agent19M0Mod2048
