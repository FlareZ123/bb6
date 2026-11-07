/-
Provisional candidate: the standalone local arithmetic and prior-sieve
models compile under Lean 4.36.0-rc2. This exact imported-source module has
not yet been locally compiled against its dependency closure or accepted by
manual original-source CI. Do not promote its claims until that check passes
and all final axiom audits exclude sorryAx.
-/
import HighEvenRightC23FullForcedResidual
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent19M1FullForced

/-- The m=1, j=24 (mod 256) high stopping progression. -/
private theorem target_x (t : Nat) :
    2*(256*t+24)+3 = 512*t+51 := by omega

private theorem target_y (t : Nat) :
    2^(2*1+2)*((256*t+24)+3)-((256*t+24)+3*1+5) =
      3840*t+400 := by
  dsimp
  omega

/-- The four-sector source normalizer takes exactly two inverse edges
    on this entire progression: one six-residue even-right edge, then
    one odd/odd low-value edge. -/
private theorem full_forced_normalize_m1_j24_mod256 (t : Nat) :
    BB6.Agent3.fullForcedNormalize (512*t+51) (3840*t+400) =
      (3136*t+322,2528*t+259) := by
  have hO : ¬ BB6.Agent3.oddLowGate (512*t+51) (3840*t+400) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS : ¬ BB6.Agent3.evenSevenGate (512*t+51) (3840*t+400) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA : ¬ BB6.Agent3.evenAffineGate (512*t+51) (3840*t+400) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE : BB6.Agent46.sixEvenRightGate (512*t+51) (3840*t+400) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  have hx1 :
      (512*t+51)+(3840*t+400)-2 = 4352*t+449 := by omega
  have hy1 : (3840*t+400-2)/2 = 1920*t+199 := by omega
  have hO1 :
      BB6.Agent3.oddLowGate (4352*t+449) (1920*t+199) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hx2 :
      ((4352*t+449)+(1920*t+199)-4)/2 = 3136*t+322 := by omega
  have hy2 :
      ((4352*t+449)+3*(1920*t+199)-10)/4 = 2528*t+259 := by omega
  have hO2 :
      ¬ BB6.Agent3.oddLowGate (3136*t+322) (2528*t+259) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hS2 :
      ¬ BB6.Agent3.evenSevenGate (3136*t+322) (2528*t+259) := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have hA2 :
      ¬ BB6.Agent3.evenAffineGate (3136*t+322) (2528*t+259) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hE2 :
      ¬ BB6.Agent46.sixEvenRightGate (3136*t+322) (2528*t+259) := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO, dif_neg hS, dif_neg hA, dif_pos hE]
  rw [hx1,hy1]
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_pos hO1]
  rw [hx2,hy2]
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hO2, dif_neg hS2, dif_neg hA2, dif_neg hE2]

/-- The terminal odd-right state violates the exact odd-image invariant. -/
private theorem full_forced_excluded_m1_j24_mod256 (t : Nat) :
    BB6.Agent3.fullForcedExcluded (512*t+51) (3840*t+400) = true := by
  simp [BB6.Agent3.fullForcedExcluded,
    full_forced_normalize_m1_j24_mod256]
  omega

/-- The progression is admitted by every previously integrated high sieve:
    the joint rectangle, all dyadic depths, the four Agent19 special classes,
    Agent29's mod-128 classes, ValSix, Agent11's image conditions,
    C58's depth tower, all-phase, C70, C23, and the earlier even-right gate. -/
theorem prior_high_allowed_m1_j24_mod256 (t : Nat) :
    BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight
      (256*t+24) 1 := by
  let j := 256*t+24
  have hjoint : BB6.Agent3.jointHighAllowed j 1 := by
    unfold BB6.Agent3.jointHighAllowed
    dsimp [j]
    refine ⟨?_,?_,?_,?_,?_⟩ <;> omega
  have hrect : BB6.Agent3.jointHighRectAllowed j 1 := by
    unfold BB6.Agent3.jointHighRectAllowed
    exact ⟨hjoint, by dsimp [j]; omega⟩
  have hdyadic : ∀ n : Nat, ¬(n+4≤2*1+2 ∧
      (j+3*1+3)%2^(n+4)=2^(n+2) ∧
      (2*j+3)%8=(if n%2=0 then 7 else 3)) := by
    intro n
    rintro ⟨hwidth,hpair,hx⟩
    have hn : n=0 := by omega
    subst n
    dsimp [j] at hpair hx
    omega
  have h19 : BB6.Agent19Joint.highAllowed j 1 := by
    unfold BB6.Agent19Joint.highAllowed
    exact ⟨hrect,hdyadic,by omega,by omega,by omega,by omega⟩
  have h29 : BB6.Agent29Joint.highAllowedPlus j 1 := by
    unfold BB6.Agent29Joint.highAllowedPlus
    exact ⟨h19,by omega,by omega,by omega,by omega⟩
  have hValSix : BB6.Agent3ValSix.highAllowedValSix j 1 := by
    unfold BB6.Agent3ValSix.highAllowedValSix
    exact ⟨h29,by omega,by omega⟩
  have hValSixThree : BB6.Agent3ValSix.highAllowedValSixThree j 1 := by
    unfold BB6.Agent3ValSix.highAllowedValSixThree
    exact ⟨hValSix,by omega⟩
  have h11 : BB6.Agent11Joint.highAllowed j 1 := by
    unfold BB6.Agent11Joint.highAllowed
    exact ⟨h19,by dsimp [j]; omega,by omega⟩
  have hFive : BB6.Agent19Five.highAllowed j 1 := by
    unfold BB6.Agent19Five.highAllowed
    exact ⟨h11,by omega⟩
  have hx : 2*j+3=512*t+51 := by
    dsimp [j]
    exact target_x t
  have hy :
      2^(2*1+2)*(j+3)-(j+3*1+5)=3840*t+400 := by
    dsimp [j]
    exact target_y t
  have hguard :
      ¬(4≤3840*t+400 ∧ (3840*t+400)%2=0 ∧
        ((512*t+51)+(3840*t+400))%4=1) := by
    omega
  have hnorm :
      BB6.Agent15.affineNormalize (512*t+51) (3840*t+400) =
        (512*t+51,3840*t+400) := by
    unfold BB6.Agent15.affineNormalize
    rw [dif_neg hguard]
  have hright :
      (BB6.Agent15.affineNormalize (2*j+3)
        (2^(2*1+2)*(j+3)-(j+3*1+5))).2≠4 := by
    rw [hx,hy,hnorm]
    omega
  have hValFull : BB6.Agent3ValSix.highAllowedValSixFull j 1 := by
    unfold BB6.Agent3ValSix.highAllowedValSixFull
    exact ⟨hValSixThree,hFive,by omega,by omega,by omega,hright⟩
  have hC58 : BB6.Agent11C58ValSix.highAllowed j 1 := by
    unfold BB6.Agent11C58ValSix.highAllowed
    exact ⟨hValFull,by omega⟩
  have hC58AllDepth : BB6.Agent11C58AllDepth.highAllowed j 1 := by
    unfold BB6.Agent11C58AllDepth.highAllowed
    exact ⟨hC58,by
      intro r
      rintro ⟨hr2,hm3,hrwidth,hm4,hpair⟩
      omega⟩
  have hPhase : ¬ BB6.Agent46.allPhaseExcluded j 1 := by
    unfold BB6.Agent46.allPhaseExcluded
    rintro ⟨r,hr8,hrwidth,hbranch⟩
    omega
  have hPhaseHigh : BB6.Agent24Phase.highAllowed j 1 := by
    unfold BB6.Agent24Phase.highAllowed
    exact ⟨hC58AllDepth,hPhase⟩
  have hC70 : BB6.Agent20C70.highAllowedC70 j 1 := by
    unfold BB6.Agent20C70.highAllowedC70
    exact ⟨hPhaseHigh,by omega⟩
  have hC23 : BB6.Agent20C23.highAllowedC23 j 1 := by
    unfold BB6.Agent20C23.highAllowedC23
    exact ⟨hC70,by omega⟩
  unfold BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight
  exact ⟨hC23,by omega⟩

/-- A new infinite source-excluded family admitted by the strongest
    pre-existing C70+C23+all-phase+even-right parameter criterion. -/
theorem m1_j24_mod256_new_infinite_exclusion (t : Nat) :
    BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight
      (256*t+24) 1 ∧
    BB6.Agent3.fullForcedExcluded (512*t+51) (3840*t+400)=true := by
  exact ⟨prior_high_allowed_m1_j24_mod256 t,
    full_forced_excluded_m1_j24_mod256 t⟩

/-- None of these targets belongs to the authentic blank-tape section orbit. -/
theorem m1_j24_mod256_blank_unreachable (t : Nat) :
    ¬ BB6.Agent3.CReach (512*t+51) (3840*t+400) := by
  intro hreach
  rcases hreach with ⟨time,hrun⟩
  exact (BB6.Agent3.fullForcedExcluded_sound
    (512*t+51) (3840*t+400)
    (full_forced_excluded_m1_j24_mod256 t) time) hrun

/-- The strongest executable high residual rejects the full progression. -/
theorem m1_j24_mod256_new_bool_filter (t : Nat) :
    BB6.Agent3FullForcedResidual.highAllowedC23WithEvenRightFullForcedBool
      (256*t+24) 1 = false := by
  have hprior :
      BB6.Agent3FullForcedResidual.highAllowedC23WithEvenRightBool
        (256*t+24) 1 = true :=
    (BB6.Agent3FullForcedResidual.highAllowedC23WithEvenRightBool_iff
      (256*t+24) 1).mpr (prior_high_allowed_m1_j24_mod256 t)
  have hx :
      BB6.Agent3FullForcedResidual.highTargetX (256*t+24)=512*t+51 := by
    simp [BB6.Agent3FullForcedResidual.highTargetX]
    omega
  have hy :
      BB6.Agent3FullForcedResidual.highTargetY (256*t+24) 1=3840*t+400 := by
    simp [BB6.Agent3FullForcedResidual.highTargetY]
    omega
  have hex :
      BB6.Agent3.fullForcedExcluded
        (BB6.Agent3FullForcedResidual.highTargetX (256*t+24))
        (BB6.Agent3FullForcedResidual.highTargetY (256*t+24) 1)=true := by
    rw [hx,hy]
    exact full_forced_excluded_m1_j24_mod256 t
  simp [BB6.Agent3FullForcedResidual.highAllowedC23WithEvenRightFullForcedBool,
    hprior,hex]

#print axioms full_forced_normalize_m1_j24_mod256
#print axioms full_forced_excluded_m1_j24_mod256
#print axioms prior_high_allowed_m1_j24_mod256
#print axioms m1_j24_mod256_new_infinite_exclusion
#print axioms m1_j24_mod256_blank_unreachable
#print axioms m1_j24_mod256_new_bool_filter

end BB6.Agent19M1FullForced
