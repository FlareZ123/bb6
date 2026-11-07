import HighEvenRightC23FullForcedResidual
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent19M0FullForced

/-- On the m=0 high stopping line and j=2 mod 16, the original
    odd/odd low-valuation predecessor sends the target to an odd-right
    state whose coordinate sum is 1 mod 4. -/
private theorem full_forced_normalize_m0_j16_two (s : Nat) (hs : 1≤s) :
    BB6.Agent3.fullForcedNormalize (32*s+7) (48*s+13) =
      (40*s+8,44*s+9) := by
  have hO : BB6.Agent3.oddLowGate (32*s+7) (48*s+13) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hO' : ¬ BB6.Agent3.oddLowGate (40*s+8) (44*s+9) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS' : ¬ BB6.Agent3.evenSevenGate (40*s+8) (44*s+9) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA' : ¬ BB6.Agent3.evenAffineGate (40*s+8) (44*s+9) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE' : ¬ BB6.Agent3.sixEvenRightGate (40*s+8) (44*s+9) := by
    unfold BB6.Agent3.sixEvenRightGate
    omega
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_pos hO]
  have hx : ((32*s+7)+(48*s+13)-4)/2=40*s+8 := by omega
  have hy : ((32*s+7)+3*(48*s+13)-10)/4=44*s+9 := by omega
  rw [hx,hy]
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO',dif_neg hS',dif_neg hA',dif_neg hE']

private theorem full_forced_excluded_m0_j16_two (s : Nat) (hs : 1≤s) :
    BB6.Agent3.fullForcedExcluded (32*s+7) (48*s+13)=true := by
  simp [BB6.Agent3.fullForcedExcluded,
    full_forced_normalize_m0_j16_two s hs]
  omega

/-- The entire progression j=16s+2, s≥1, survives the preceding
    C70+C23+all-phase+even-right high sieve. -/
theorem prior_high_allowed_m0_j16_two (s : Nat) (hs : 1≤s) :
    BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight (16*s+2) 0 := by
  let j := 16*s+2
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
      (BB6.Agent15.affineNormalize (32*s+7) (48*s+13)).2≠4 := by
    unfold BB6.Agent15.affineNormalize
    have hgate :
        ¬(4≤48*s+13 ∧ (48*s+13)%2=0 ∧
          ((32*s+7)+(48*s+13))%4=1) := by omega
    rw [dif_neg hgate]
    omega
  have hright :
      (BB6.Agent15.affineNormalize (2*j+3)
        (2^(2*0+2)*(j+3)-(j+3*0+5))).2≠4 := by
    simpa [j] using hright0
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

/-- A new infinite source-excluded high stopping family, previously
    admitted by the strongest existing high parameter sieve. -/
theorem m0_j_mod16_two_new_infinite_exclusion (s : Nat) (hs : 1≤s) :
    BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight (16*s+2) 0 ∧
    BB6.Agent3.fullForcedExcluded (32*s+7) (48*s+13)=true := by
  exact ⟨prior_high_allowed_m0_j16_two s hs,
    full_forced_excluded_m0_j16_two s hs⟩

/-- None of these exact high stopping targets lies on the authentic
    blank-tape section orbit, at any time. -/
theorem m0_j_mod16_two_blank_unreachable (s : Nat) (hs : 1≤s) :
    ¬ BB6.Agent3.CReach (32*s+7) (48*s+13) := by
  intro hreach
  rcases hreach with ⟨time,hrun⟩
  exact (BB6.Agent3.fullForcedExcluded_sound
    (32*s+7) (48*s+13)
    (full_forced_excluded_m0_j16_two s hs) time) hrun

/-- The new Boolean high residual rejects the whole progression. -/
theorem m0_j_mod16_two_new_bool_filter (s : Nat) (hs : 1≤s) :
    BB6.Agent3FullForcedResidual.highAllowedC23WithEvenRightFullForcedBool
      (16*s+2) 0 = false := by
  have hprior :
      BB6.Agent3FullForcedResidual.highAllowedC23WithEvenRightBool
        (16*s+2) 0 = true :=
    (BB6.Agent3FullForcedResidual.highAllowedC23WithEvenRightBool_iff
      (16*s+2) 0).mpr (prior_high_allowed_m0_j16_two s hs)
  simp [BB6.Agent3FullForcedResidual.highAllowedC23WithEvenRightFullForcedBool,
    hprior,full_forced_excluded_m0_j16_two s hs]

#print axioms prior_high_allowed_m0_j16_two
#print axioms m0_j_mod16_two_new_infinite_exclusion
#print axioms m0_j_mod16_two_blank_unreachable
#print axioms m0_j_mod16_two_new_bool_filter

end BB6.Agent19M0FullForced
