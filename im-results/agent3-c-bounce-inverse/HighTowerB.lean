import ChildBTwoDepth
import HighTowerTwoParam
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Disjoint higher-stopping tower with 4n+2 forced affine inverse edges,
    whose normalizer falls in the sharp two-edge B rectangle. -/
def highJB (q : Nat) : Nat → Nat
  | 0 => 128*q+66
  | n+1 => 16*highJB q n+42

def rightB (q : Nat) : Nat → Nat
  | 0 => 480*q+256
  | d+1 => 2*rightB q d+2

private theorem highJB_mod4 (q n : Nat) : highJB q n%4=2 := by
  induction n with
  | zero => change (128*q+66)%4=2; omega
  | succ n ih => change (16*highJB q n+42)%4=2; omega

private theorem rightB_even (q d : Nat) : rightB q d%2=0 := by
  cases d with
  | zero => change (480*q+256)%2=0; omega
  | succ d => change (2*rightB q d+2)%2=0; omega

private theorem rightB_lower (q d : Nat) : 256≤rightB q d := by
  induction d with
  | zero => change 256≤480*q+256; omega
  | succ d ih => change 256≤2*rightB q d+2; omega

private theorem rightB_four (q d : Nat) :
    rightB q (d+4)=16*rightB q d+30 := by
  have hd : d+4=d+1+1+1+1 := by omega
  rw [hd]
  simp only [rightB]
  omega

private theorem highB_right_eq (q n : Nat) :
    rightB q (4*n+2)=15*highJB q n+40 := by
  induction n with
  | zero =>
      change 2*(2*(480*q+256)+2)+2=15*(128*q+66)+40
      omega
  | succ n ih =>
      have hd : 4*(n+1)+2=(4*n+2)+4 := by omega
      rw [hd,rightB_four]
      change 16*rightB q (4*n+2)+30=15*(16*highJB q n+42)+40
      rw [ih]
      omega

theorem highB_right_tower (q n : Nat) :
    rightB q (4*n+2)=15*highJB q n+40 := highB_right_eq q n

private theorem rightB_depth (q d : Nat) :
    BB6.Agent15.oddDepth (rightB q d)=d := by
  induction d with
  | zero =>
      have hn : ¬(4≤480*q+256 ∧ (480*q+256)%4=2) := by omega
      change BB6.Agent15.oddDepth (480*q+256)=0
      rw [BB6.Agent15.oddDepth,dif_neg hn]
  | succ d ih =>
      have he := rightB_even q d
      have hl := rightB_lower q d
      have hg : 4≤rightB q (d+1) ∧ rightB q (d+1)%4=2 := by
        simp only [rightB]
        omega
      have hr : (rightB q (d+1)-2)/2=rightB q d := by
        simp only [rightB]
        omega
      rw [BB6.Agent15.oddDepth,dif_pos hg,hr,ih]
      omega

private theorem rightB_terminal (q d a : Nat) (ha : a%4=3) :
    (BB6.Agent15.affineNormalize a (rightB q d)).2=480*q+256 := by
  induction d generalizing a with
  | zero =>
      have hn : ¬(4≤480*q+256 ∧ (480*q+256)%2=0 ∧
        (a+(480*q+256))%4=1) := by omega
      change (BB6.Agent15.affineNormalize a (480*q+256)).2=480*q+256
      rw [BB6.Agent15.affineNormalize,dif_neg hn]
  | succ d ih =>
      have he := rightB_even q d
      have hl := rightB_lower q d
      have hg : 4≤rightB q (d+1) ∧
          rightB q (d+1)%2=0 ∧
          (a+rightB q (d+1))%4=1 := by
        simp only [rightB]
        omega
      have ha' : (a+rightB q (d+1)-2)%4=3 := by
        simp only [rightB]
        omega
      have hr : (rightB q (d+1)-2)/2=rightB q d := by
        simp only [rightB]
        omega
      rw [BB6.Agent15.affineNormalize,dif_pos hg,hr]
      exact ih (a+rightB q (d+1)-2) ha'

theorem highB_halt_input (q n : Nat) :
    secNext (2*highJB q n+3,15*highJB q n+40)=none := by
  apply (BB6.Agent15.section_halts_iff_parametric _ _).mpr
  right
  right
  refine ⟨highJB q n,1,by omega,?_⟩
  change (15*highJB q n+40)+highJB q n+3*1+5=16*(highJB q n+3)
  omega

theorem highB_exact_depth (q n : Nat) :
    BB6.Agent15.oddDepth (15*highJB q n+40)=4*n+2 := by
  rw [←highB_right_eq q n]
  exact rightB_depth q (4*n+2)

theorem highB_normalized_cone (q n : Nat) :
    let p := BB6.Agent15.affineNormalize
      (2*highJB q n+3) (15*highJB q n+40)
    p.1%16=11 ∧ p.2%32=0 ∧ 32≤p.2 := by
  have hj := highJB_mod4 q n
  have ha : (2*highJB q n+3)%4=3 := by omega
  have hright : (BB6.Agent15.affineNormalize
      (2*highJB q n+3) (15*highJB q n+40)).2=480*q+256 := by
    rw [←highB_right_eq q n]
    exact rightB_terminal q (4*n+2) (2*highJB q n+3) ha
  have hdepth := highB_exact_depth q n
  have hmass := (BB6.Agent15.normalize_three_depth_invariants
    (2*highJB q n+3) (15*highJB q n+40) ha).1
  have heq : (BB6.Agent15.affineNormalize
    (2*highJB q n+3) (15*highJB q n+40)).1+2*(480*q+256)+4*(4*n+2)=
    (2*highJB q n+3)+2*(15*highJB q n+40) := by
    simpa only [hright,hdepth] using hmass
  dsimp
  omega

theorem highB_blank_unreachable (q n : Nat) :
    ¬ BB6.Agent15.CReach (2*highJB q n+3) (15*highJB q n+40) := by
  intro hr
  have hnorm := (BB6.Agent15.reach_iff_normalize
    (2*highJB q n+3) (15*highJB q n+40)).mp hr
  obtain ⟨time,ht⟩ := hnorm
  have hc := highB_normalized_cone q n
  let p := BB6.Agent15.affineNormalize
    (2*highJB q n+3) (15*highJB q n+40)
  let u := p.1/16
  let v := (p.2-32)/32
  have hc1 : p.1%16=11 := hc.1
  have hc2 : p.2%32=0 := hc.2.1
  have hc3 : 32≤p.2 := hc.2.2
  have hx : p.1=16*u+11 := by dsimp [u]; omega
  have hy : p.2=32*v+32 := by dsimp [v]; omega
  rw [hx,hy] at ht
  exact even_child_B_unreachable u v time ht

theorem highB_power_identity (q n : Nat) :
    15*highJB q n+42=16^n*(1920*q+1032) := by
  induction n with
  | zero =>
      change 15*(128*q+66)+42=16^0*(1920*q+1032)
      omega
  | succ n ih =>
      calc
        15*highJB q (n+1)+42 = 16*(15*highJB q n+42) := by
          change 15*(16*highJB q n+42)+42 = 16*(15*highJB q n+42)
          omega
        _ = 16*(16^n*(1920*q+1032)) := by rw [ih]
        _ = 16^(n+1)*(1920*q+1032) := by
          simp only [Nat.pow_succ]
          ac_rfl

#print axioms highB_halt_input
#print axioms highB_exact_depth
#print axioms highB_normalized_cone
#print axioms highB_blank_unreachable
#print axioms highB_power_identity
end BB6.Agent3
