/-
Provisional candidate: the standalone local arithmetic and prior-sieve
models compile under Lean 4.36.0-rc2. This exact imported-source module has
not yet been locally compiled against its dependency closure or accepted by
manual original-source CI. Do not promote its claims until that check passes
and all final axiom audits exclude sorryAx.
-/
import HighM1FullForced
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent19M2FullForced

private theorem target_x (t : Nat) :
    2*(32*t+9)+3 = 64*t+21 := by omega

private theorem target_y (t : Nat) :
    2^(2*2+2)*((32*t+9)+3)-((32*t+9)+3*2+5) =
      2016*t+748 := by
  dsimp
  omega

/-- The m=2, j=9 (mod 32) target has an even-affine inverse followed
    by an odd/odd low-value inverse. -/
private theorem full_forced_normalize_m2_j9_mod32 (t : Nat) :
    BB6.Agent3.fullForcedNormalize (64*t+21) (2016*t+748) =
      (1544*t+568,1276*t+469) := by
  have hO : ¬ BB6.Agent3.oddLowGate (64*t+21) (2016*t+748) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS : ¬ BB6.Agent3.evenSevenGate (64*t+21) (2016*t+748) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA : BB6.Agent3.evenAffineGate (64*t+21) (2016*t+748) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hx1 :
      (64*t+21)+(2016*t+748)-2 = 2080*t+767 := by omega
  have hy1 : (2016*t+748-2)/2 = 1008*t+373 := by omega
  have hO1 :
      BB6.Agent3.oddLowGate (2080*t+767) (1008*t+373) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hx2 :
      ((2080*t+767)+(1008*t+373)-4)/2 = 1544*t+568 := by omega
  have hy2 :
      ((2080*t+767)+3*(1008*t+373)-10)/4 = 1276*t+469 := by omega
  have hO2 :
      ¬ BB6.Agent3.oddLowGate (1544*t+568) (1276*t+469) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS2 :
      ¬ BB6.Agent3.evenSevenGate (1544*t+568) (1276*t+469) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA2 :
      ¬ BB6.Agent3.evenAffineGate (1544*t+568) (1276*t+469) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE2 :
      ¬ BB6.Agent46.sixEvenRightGate (1544*t+568) (1276*t+469) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO, dif_neg hS, dif_pos hA]
  rw [hx1,hy1]
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_pos hO1]
  rw [hx2,hy2]
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO2, dif_neg hS2, dif_neg hA2, dif_neg hE2]

private theorem full_forced_excluded_m2_j9_mod32 (t : Nat) :
    BB6.Agent3.fullForcedExcluded (64*t+21) (2016*t+748) = true := by
  simp [BB6.Agent3.fullForcedExcluded,
    full_forced_normalize_m2_j9_mod32]
  omega

/-- This progression survives all previously integrated high source filters.
    The affine-right-four gate performs one step and stops at an odd right
    coordinate, so it also does not remove the progression. -/
theorem prior_high_allowed_m2_j9_mod32 (t : Nat) :
    BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight
      (32*t+9) 2 := by
  let j := 32*t+9
  have hjoint : BB6.Agent3.jointHighAllowed j 2 := by
    unfold BB6.Agent3.jointHighAllowed
    dsimp [j]
    refine ⟨?_,?_,?_,?_,?_⟩ <;> omega
  have hrect : BB6.Agent3.jointHighRectAllowed j 2 := by
    unfold BB6.Agent3.jointHighRectAllowed
    exact ⟨hjoint, by dsimp [j]; omega⟩
  have hdyadic : ∀ n : Nat, ¬(n+4≤2*2+2 ∧
      (j+3*2+3)%2^(n+4)=2^(n+2) ∧
      (2*j+3)%8=(if n%2=0 then 7 else 3)) := by
    intro n
    rintro ⟨hwidth,hpair,hx⟩
    have hx5 : (2*j+3)%8=5 := by
      dsimp [j]
      omega
    rw [hx5] at hx
    by_cases hn : n%2=0
    · simp [hn] at hx
    · simp [hn] at hx
  have h19 : BB6.Agent19Joint.highAllowed j 2 := by
    unfold BB6.Agent19Joint.highAllowed
    exact ⟨hrect,hdyadic,by omega,by omega,by omega,by omega⟩
  have h29 : BB6.Agent29Joint.highAllowedPlus j 2 := by
    unfold BB6.Agent29Joint.highAllowedPlus
    exact ⟨h19,by omega,by omega,by omega,by omega⟩
  have hValSix : BB6.Agent3ValSix.highAllowedValSix j 2 := by
    unfold BB6.Agent3ValSix.highAllowedValSix
    exact ⟨h29,by omega,by omega⟩
  have hValSixThree : BB6.Agent3ValSix.highAllowedValSixThree j 2 := by
    unfold BB6.Agent3ValSix.highAllowedValSixThree
    exact ⟨hValSix,by omega⟩
  have h11 : BB6.Agent11Joint.highAllowed j 2 := by
    unfold BB6.Agent11Joint.highAllowed
    exact ⟨h19,by dsimp [j]; omega,by omega⟩
  have hFive : BB6.Agent19Five.highAllowed j 2 := by
    unfold BB6.Agent19Five.highAllowed
    exact ⟨h11,by omega⟩
  have hx : 2*j+3=64*t+21 := by
    dsimp [j]
    exact target_x t
  have hy :
      2^(2*2+2)*(j+3)-(j+3*2+5)=2016*t+748 := by
    dsimp [j]
    exact target_y t
  have hguard :
      4≤2016*t+748 ∧ (2016*t+748)%2=0 ∧
        ((64*t+21)+(2016*t+748))%4=1 := by
    omega
  have hx1 :
      (64*t+21)+(2016*t+748)-2=2080*t+767 := by omega
  have hy1 : (2016*t+748-2)/2=1008*t+373 := by omega
  have hguard1 :
      ¬(4≤1008*t+373 ∧ (1008*t+373)%2=0 ∧
        ((2080*t+767)+(1008*t+373))%4=1) := by
    omega
  have hnorm :
      BB6.Agent15.affineNormalize (64*t+21) (2016*t+748) =
        (2080*t+767,1008*t+373) := by
    unfold BB6.Agent15.affineNormalize
    rw [dif_pos hguard]
    rw [hx1,hy1]
    unfold BB6.Agent15.affineNormalize
    rw [dif_neg hguard1]
  have hright :
      (BB6.Agent15.affineNormalize (2*j+3)
        (2^(2*2+2)*(j+3)-(j+3*2+5))).2≠4 := by
    rw [hx,hy,hnorm]
    omega
  have hValFull : BB6.Agent3ValSix.highAllowedValSixFull j 2 := by
    unfold BB6.Agent3ValSix.highAllowedValSixFull
    exact ⟨hValSixThree,hFive,by omega,by omega,by omega,hright⟩
  have hC58 : BB6.Agent11C58ValSix.highAllowed j 2 := by
    unfold BB6.Agent11C58ValSix.highAllowed
    exact ⟨hValFull,by omega⟩
  have hC58AllDepth : BB6.Agent11C58AllDepth.highAllowed j 2 := by
    unfold BB6.Agent11C58AllDepth.highAllowed
    exact ⟨hC58,by
      intro r
      rintro ⟨hr2,hm3,hrwidth,hm4,hpair⟩
      omega⟩
  have hPhase : ¬ BB6.Agent46.allPhaseExcluded j 2 := by
    unfold BB6.Agent46.allPhaseExcluded
    rintro ⟨r,hr8,hrwidth,hbranch⟩
    omega
  have hPhaseHigh : BB6.Agent24Phase.highAllowed j 2 := by
    unfold BB6.Agent24Phase.highAllowed
    exact ⟨hC58AllDepth,hPhase⟩
  have hC70 : BB6.Agent20C70.highAllowedC70 j 2 := by
    unfold BB6.Agent20C70.highAllowedC70
    exact ⟨hPhaseHigh,by omega⟩
  have hC23 : BB6.Agent20C23.highAllowedC23 j 2 := by
    unfold BB6.Agent20C23.highAllowedC23
    exact ⟨hC70,by omega⟩
  unfold BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight
  exact ⟨hC23,by omega⟩

theorem m2_j9_mod32_new_infinite_exclusion (t : Nat) :
    BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight
      (32*t+9) 2 ∧
    BB6.Agent3.fullForcedExcluded (64*t+21) (2016*t+748)=true := by
  exact ⟨prior_high_allowed_m2_j9_mod32 t,
    full_forced_excluded_m2_j9_mod32 t⟩

theorem m2_j9_mod32_blank_unreachable (t : Nat) :
    ¬ BB6.Agent3.CReach (64*t+21) (2016*t+748) := by
  intro hreach
  rcases hreach with ⟨time,hrun⟩
  exact (BB6.Agent3.fullForcedExcluded_sound
    (64*t+21) (2016*t+748)
    (full_forced_excluded_m2_j9_mod32 t) time) hrun

theorem m2_j9_mod32_new_bool_filter (t : Nat) :
    BB6.Agent3FullForcedResidual.highAllowedC23WithEvenRightFullForcedBool
      (32*t+9) 2 = false := by
  have hprior :
      BB6.Agent3FullForcedResidual.highAllowedC23WithEvenRightBool
        (32*t+9) 2 = true :=
    (BB6.Agent3FullForcedResidual.highAllowedC23WithEvenRightBool_iff
      (32*t+9) 2).mpr (prior_high_allowed_m2_j9_mod32 t)
  have hx :
      BB6.Agent3FullForcedResidual.highTargetX (32*t+9)=64*t+21 := by
    simp [BB6.Agent3FullForcedResidual.highTargetX]
    omega
  have hy :
      BB6.Agent3FullForcedResidual.highTargetY (32*t+9) 2=2016*t+748 := by
    simp [BB6.Agent3FullForcedResidual.highTargetY]
    omega
  have hex :
      BB6.Agent3.fullForcedExcluded
        (BB6.Agent3FullForcedResidual.highTargetX (32*t+9))
        (BB6.Agent3FullForcedResidual.highTargetY (32*t+9) 2)=true := by
    rw [hx,hy]
    exact full_forced_excluded_m2_j9_mod32 t
  simp [BB6.Agent3FullForcedResidual.highAllowedC23WithEvenRightFullForcedBool,
    hprior,hex]

#print axioms full_forced_normalize_m2_j9_mod32
#print axioms full_forced_excluded_m2_j9_mod32
#print axioms prior_high_allowed_m2_j9_mod32
#print axioms m2_j9_mod32_new_infinite_exclusion
#print axioms m2_j9_mod32_blank_unreachable
#print axioms m2_j9_mod32_new_bool_filter

end BB6.Agent19M2FullForced
