import HighEvenRightC23FullForcedResidual
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent12M0Lift

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

/-- The exact 15-gate source normalizer path for the last finite
    m=0 high residual j=1093, lifted to a 2^22 progression. The stride
    preserves the modulus required at every gate and by the prior sieve. -/
private theorem normalize_m0_2p22_1093 (t : Nat) :
    BB6.Agent3.fullForcedNormalize (8388608*t+2189) (12582912*t+3286) =
      (29087208*t+7532,2233612*t+577) := by
  have g0 : ¬BB6.Agent3.oddLowGate (8388608*t+2189) (12582912*t+3286) ∧
      ¬BB6.Agent3.evenSevenGate (8388608*t+2189) (12582912*t+3286) ∧
      ¬BB6.Agent3.evenAffineGate (8388608*t+2189) (12582912*t+3286) ∧
      BB6.Agent46.sixEvenRightGate (8388608*t+2189) (12582912*t+3286) := by
    unfold BB6.Agent3.oddLowGate BB6.Agent3.evenSevenGate
      BB6.Agent3.evenAffineGate BB6.Agent46.sixEvenRightGate
    omega
  rcases g0 with ⟨hO0,hS0,hA0,hE0⟩

  have g1 : ¬BB6.Agent3.oddLowGate (20971520*t+5473) (6291456*t+1642) ∧
      ¬BB6.Agent3.evenSevenGate (20971520*t+5473) (6291456*t+1642) ∧
      ¬BB6.Agent3.evenAffineGate (20971520*t+5473) (6291456*t+1642) ∧
      BB6.Agent46.sixEvenRightGate (20971520*t+5473) (6291456*t+1642) := by
    unfold BB6.Agent3.oddLowGate BB6.Agent3.evenSevenGate
      BB6.Agent3.evenAffineGate BB6.Agent46.sixEvenRightGate
    omega
  rcases g1 with ⟨hO1,hS1,hA1,hE1⟩

  have g2 : ¬BB6.Agent3.oddLowGate (27262976*t+7113) (3145728*t+820) ∧
      ¬BB6.Agent3.evenSevenGate (27262976*t+7113) (3145728*t+820) ∧
      BB6.Agent3.evenAffineGate (27262976*t+7113) (3145728*t+820) := by
    unfold BB6.Agent3.oddLowGate BB6.Agent3.evenSevenGate
      BB6.Agent3.evenAffineGate
    omega
  rcases g2 with ⟨hO2,hS2,hA2⟩

  have hO3 : BB6.Agent3.oddLowGate (30408704*t+7931) (1572864*t+409) := by
    unfold BB6.Agent3.oddLowGate
    omega

  have g4 : ¬BB6.Agent3.oddLowGate (15990784*t+4168) (8781824*t+2287) ∧
      BB6.Agent3.evenSevenGate (15990784*t+4168) (8781824*t+2287) := by
    unfold BB6.Agent3.oddLowGate BB6.Agent3.evenSevenGate
    omega
  rcases g4 with ⟨hO4,hS4⟩

  have hO5 : BB6.Agent3.oddLowGate (12386304*t+3225) (10584064*t+2755) := by
    unfold BB6.Agent3.oddLowGate
    omega

  have g6 : ¬BB6.Agent3.oddLowGate (11485184*t+2988) (11034624*t+2870) ∧
      ¬BB6.Agent3.evenSevenGate (11485184*t+2988) (11034624*t+2870) ∧
      ¬BB6.Agent3.evenAffineGate (11485184*t+2988) (11034624*t+2870) ∧
      BB6.Agent46.sixEvenRightGate (11485184*t+2988) (11034624*t+2870) := by
    unfold BB6.Agent3.oddLowGate BB6.Agent3.evenSevenGate
      BB6.Agent3.evenAffineGate BB6.Agent46.sixEvenRightGate
    omega
  rcases g6 with ⟨hO6,hS6,hA6,hE6⟩

  have g7 : ¬BB6.Agent3.oddLowGate (22519808*t+5856) (5517312*t+1434) ∧
      ¬BB6.Agent3.evenSevenGate (22519808*t+5856) (5517312*t+1434) ∧
      ¬BB6.Agent3.evenAffineGate (22519808*t+5856) (5517312*t+1434) ∧
      BB6.Agent46.sixEvenRightGate (22519808*t+5856) (5517312*t+1434) := by
    unfold BB6.Agent3.oddLowGate BB6.Agent3.evenSevenGate
      BB6.Agent3.evenAffineGate BB6.Agent46.sixEvenRightGate
    omega
  rcases g7 with ⟨hO7,hS7,hA7,hE7⟩

  have g8 : ¬BB6.Agent3.oddLowGate (28037120*t+7288) (2758656*t+716) ∧
      ¬BB6.Agent3.evenSevenGate (28037120*t+7288) (2758656*t+716) ∧
      ¬BB6.Agent3.evenAffineGate (28037120*t+7288) (2758656*t+716) ∧
      BB6.Agent46.sixEvenRightGate (28037120*t+7288) (2758656*t+716) := by
    unfold BB6.Agent3.oddLowGate BB6.Agent3.evenSevenGate
      BB6.Agent3.evenAffineGate BB6.Agent46.sixEvenRightGate
    omega
  rcases g8 with ⟨hO8,hS8,hA8,hE8⟩

  have g9 : ¬BB6.Agent3.oddLowGate (30795776*t+8002) (1379328*t+357) ∧
      BB6.Agent3.evenSevenGate (30795776*t+8002) (1379328*t+357) := by
    unfold BB6.Agent3.oddLowGate BB6.Agent3.evenSevenGate
    omega
  rcases g9 with ⟨hO9,hS9⟩

  have g10 : ¬BB6.Agent3.oddLowGate (16087552*t+4177) (8733440*t+2266) ∧
      ¬BB6.Agent3.evenSevenGate (16087552*t+4177) (8733440*t+2266) ∧
      ¬BB6.Agent3.evenAffineGate (16087552*t+4177) (8733440*t+2266) ∧
      BB6.Agent46.sixEvenRightGate (16087552*t+4177) (8733440*t+2266) := by
    unfold BB6.Agent3.oddLowGate BB6.Agent3.evenSevenGate
      BB6.Agent3.evenAffineGate BB6.Agent46.sixEvenRightGate
    omega
  rcases g10 with ⟨hO10,hS10,hA10,hE10⟩

  have g11 : ¬BB6.Agent3.oddLowGate (24820992*t+6441) (4366720*t+1132) ∧
      ¬BB6.Agent3.evenSevenGate (24820992*t+6441) (4366720*t+1132) ∧
      BB6.Agent3.evenAffineGate (24820992*t+6441) (4366720*t+1132) := by
    unfold BB6.Agent3.oddLowGate BB6.Agent3.evenSevenGate
      BB6.Agent3.evenAffineGate
    omega
  rcases g11 with ⟨hO11,hS11,hA11⟩

  have hO12 : BB6.Agent3.oddLowGate (29187712*t+7571) (2183360*t+565) := by
    unfold BB6.Agent3.oddLowGate
    omega

  have g13 : ¬BB6.Agent3.oddLowGate (15685536*t+4066) (8934448*t+2314) ∧
      ¬BB6.Agent3.evenSevenGate (15685536*t+4066) (8934448*t+2314) ∧
      ¬BB6.Agent3.evenAffineGate (15685536*t+4066) (8934448*t+2314) ∧
      BB6.Agent46.sixEvenRightGate (15685536*t+4066) (8934448*t+2314) := by
    unfold BB6.Agent3.oddLowGate BB6.Agent3.evenSevenGate
      BB6.Agent3.evenAffineGate BB6.Agent46.sixEvenRightGate
    omega
  rcases g13 with ⟨hO13,hS13,hA13,hE13⟩

  have g14 : ¬BB6.Agent3.oddLowGate (24619984*t+6378) (4467224*t+1156) ∧
      ¬BB6.Agent3.evenSevenGate (24619984*t+6378) (4467224*t+1156) ∧
      ¬BB6.Agent3.evenAffineGate (24619984*t+6378) (4467224*t+1156) ∧
      BB6.Agent46.sixEvenRightGate (24619984*t+6378) (4467224*t+1156) := by
    unfold BB6.Agent3.oddLowGate BB6.Agent3.evenSevenGate
      BB6.Agent3.evenAffineGate BB6.Agent46.sixEvenRightGate
    omega
  rcases g14 with ⟨hO14,hS14,hA14,hE14⟩

  have g15 : ¬BB6.Agent3.oddLowGate (29087208*t+7532) (2233612*t+577) ∧
      ¬BB6.Agent3.evenSevenGate (29087208*t+7532) (2233612*t+577) ∧
      ¬BB6.Agent3.evenAffineGate (29087208*t+7532) (2233612*t+577) ∧
      ¬BB6.Agent46.sixEvenRightGate (29087208*t+7532) (2233612*t+577) := by
    unfold BB6.Agent3.oddLowGate BB6.Agent3.evenSevenGate
      BB6.Agent3.evenAffineGate BB6.Agent46.sixEvenRightGate
    omega
  rcases g15 with ⟨hO15,hS15,hA15,hE15⟩

  calc
    BB6.Agent3.fullForcedNormalize (8388608*t+2189) (12582912*t+3286) =
        BB6.Agent3.fullForcedNormalize (20971520*t+5473) (6291456*t+1642) :=
      forced_step_six hO0 hS0 hA0 hE0 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (27262976*t+7113) (3145728*t+820) :=
      forced_step_six hO1 hS1 hA1 hE1 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (30408704*t+7931) (1572864*t+409) :=
      forced_step_affine hO2 hS2 hA2 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (15990784*t+4168) (8781824*t+2287) :=
      forced_step_odd hO3 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (12386304*t+3225) (10584064*t+2755) :=
      forced_step_seven hO4 hS4 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (11485184*t+2988) (11034624*t+2870) :=
      forced_step_odd hO5 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (22519808*t+5856) (5517312*t+1434) :=
      forced_step_six hO6 hS6 hA6 hE6 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (28037120*t+7288) (2758656*t+716) :=
      forced_step_six hO7 hS7 hA7 hE7 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (30795776*t+8002) (1379328*t+357) :=
      forced_step_six hO8 hS8 hA8 hE8 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (16087552*t+4177) (8733440*t+2266) :=
      forced_step_seven hO9 hS9 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (24820992*t+6441) (4366720*t+1132) :=
      forced_step_six hO10 hS10 hA10 hE10 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (29187712*t+7571) (2183360*t+565) :=
      forced_step_affine hO11 hS11 hA11 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (15685536*t+4066) (8934448*t+2314) :=
      forced_step_odd hO12 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (24619984*t+6378) (4467224*t+1156) :=
      forced_step_six hO13 hS13 hA13 hE13 (by omega) (by omega)
    _ = BB6.Agent3.fullForcedNormalize (29087208*t+7532) (2233612*t+577) :=
      forced_step_six hO14 hS14 hA14 hE14 (by omega) (by omega)
    _ = (29087208*t+7532,2233612*t+577) :=
      forced_terminal hO15 hS15 hA15 hE15

private theorem excluded_m0_2p22_1093 (t : Nat) :
    BB6.Agent3.fullForcedExcluded (8388608*t+2189) (12582912*t+3286)=true := by
  simp [BB6.Agent3.fullForcedExcluded,normalize_m0_2p22_1093]
  omega

private theorem affine_right_m0_2p22_1093 (t : Nat) :
    (BB6.Agent15.affineNormalize (8388608*t+2189)
      (12582912*t+3286)).2≠4 := by
  apply affine_right_no_step
  · unfold BB6.Agent15.affineNormalize
    omega
  · omega

/-- A new infinite m=0 high-stopping family, disjoint from the
    previously certified progressions: j=2^22*t+1093. -/
theorem m0_2p22_1093_admitted_and_excluded (t : Nat) :
    BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight
        (4194304*t+1093) 0 ∧
      BB6.Agent3.fullForcedExcluded (8388608*t+2189)
        (12582912*t+3286)=true := by
  constructor
  · apply prior_high_allowed_m0
    · omega
    · simpa [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using
        affine_right_m0_2p22_1093 t
  · exact excluded_m0_2p22_1093 t

/-- No target in this exact high-stopping family lies on the original
    blank-tape section orbit, at any time. -/
theorem m0_2p22_1093_blank_unreachable (t : Nat) :
    ¬ BB6.Agent3.CReach (8388608*t+2189) (12582912*t+3286) := by
  intro h
  rcases h with ⟨time,hr⟩
  exact (BB6.Agent3.fullForcedExcluded_sound _ _
    (excluded_m0_2p22_1093 t) time) hr

#print axioms prior_high_allowed_m0
#print axioms normalize_m0_2p22_1093
#print axioms m0_2p22_1093_admitted_and_excluded
#print axioms m0_2p22_1093_blank_unreachable

end BB6.Agent12M0Lift
