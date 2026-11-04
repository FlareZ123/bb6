import EvenChildSevenFour
import AffineNormalize
import SectionParam
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 10000

namespace BB6.Agent3
open BB6.Agent46

/-- The authentic affine normalizer has exactly five forced predecessors
    on each member of this explicit infinite higher-stopping family. -/
theorem m1_five_tower_normalize (t : Nat) :
    BB6.Agent15.affineNormalize (512*t+535) (3840*t+4030) =
    (7952*t+8327,120*t+124) := by
  have gate0 : 4≤3840*t+4030 ∧ (3840*t+4030)%2=0 ∧ ((512*t+535)+(3840*t+4030))%4=1 := by omega
  rw [BB6.Agent15.affineNormalize, dif_pos gate0]
  have ae0 : (512*t+535)+(3840*t+4030)-2=4352*t+4563 := by omega
  have ke0 : ((3840*t+4030)-2)/2=1920*t+2014 := by omega
  rw [ae0,ke0]
  have gate1 : 4≤1920*t+2014 ∧ (1920*t+2014)%2=0 ∧ ((4352*t+4563)+(1920*t+2014))%4=1 := by omega
  rw [BB6.Agent15.affineNormalize, dif_pos gate1]
  have ae1 : (4352*t+4563)+(1920*t+2014)-2=6272*t+6575 := by omega
  have ke1 : ((1920*t+2014)-2)/2=960*t+1006 := by omega
  rw [ae1,ke1]
  have gate2 : 4≤960*t+1006 ∧ (960*t+1006)%2=0 ∧ ((6272*t+6575)+(960*t+1006))%4=1 := by omega
  rw [BB6.Agent15.affineNormalize, dif_pos gate2]
  have ae2 : (6272*t+6575)+(960*t+1006)-2=7232*t+7579 := by omega
  have ke2 : ((960*t+1006)-2)/2=480*t+502 := by omega
  rw [ae2,ke2]
  have gate3 : 4≤480*t+502 ∧ (480*t+502)%2=0 ∧ ((7232*t+7579)+(480*t+502))%4=1 := by omega
  rw [BB6.Agent15.affineNormalize, dif_pos gate3]
  have ae3 : (7232*t+7579)+(480*t+502)-2=7712*t+8079 := by omega
  have ke3 : ((480*t+502)-2)/2=240*t+250 := by omega
  rw [ae3,ke3]
  have gate4 : 4≤240*t+250 ∧ (240*t+250)%2=0 ∧ ((7712*t+8079)+(240*t+250))%4=1 := by omega
  rw [BB6.Agent15.affineNormalize, dif_pos gate4]
  have ae4 : (7712*t+8079)+(240*t+250)-2=7952*t+8327 := by omega
  have ke4 : ((240*t+250)-2)/2=120*t+124 := by omega
  rw [ae4,ke4]
  have stop : ¬(4≤120*t+124 ∧ (120*t+124)%2=0 ∧ ((7952*t+8327)+(120*t+124))%4=1) := by omega
  rw [BB6.Agent15.affineNormalize, dif_neg stop]

/-- Source-exact stopping equation for m=1 and j=256*t+266. -/
theorem m1_five_tower_stop (t : Nat) :
    secNext (512*t+535,3840*t+4030)=none := by
  apply (BB6.Agent15.section_halts_iff_parametric _ _).mpr
  right
  right
  refine ⟨256*t+266,1,by omega,?_⟩
  change (3840*t+4030)+(256*t+266)+3*1+5 = 16*((256*t+266)+3)
  omega

/-- Source-verified infinite family of genuine stopping states absent
    from the blank section, even though the reproduced B8/M256
    numerical abstraction admits each original target. -/
theorem m1_five_tower_unreachable (t : Nat) :
    ¬ BB6.Agent15.CReach (512*t+535) (3840*t+4030) := by
  intro hr
  have h := (BB6.Agent15.reach_iff_normalize (512*t+535) (3840*t+4030)).mp hr
  rw [m1_five_tower_normalize] at h
  obtain ⟨n,hn⟩ := h
  exact (seven_four_blank_unreachable n (7952*t+8327) (120*t+124)
    (by omega) (by omega) (by omega)) hn

#print axioms m1_five_tower_normalize
#print axioms m1_five_tower_stop
#print axioms m1_five_tower_unreachable
end BB6.Agent3
