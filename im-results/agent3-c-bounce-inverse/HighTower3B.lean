import ChildBTwoDepth
import HighTowerTwoParam
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Disjoint higher-stopping tower with 8n+3 forced affine inverse edges,
    whose normalizer falls in the sharp two-edge B rectangle. -/
def highJ3B (q : Nat) : Nat → Nat
  | 0 => 256*q+228
  | n+1 => 256*highJ3B q n+756

def right3B (q : Nat) : Nat → Nat
  | 0 => 8160*q+7360
  | d+1 => 2*right3B q d+2

private theorem highJ3B_mod4 (q n : Nat) : highJ3B q n%4=0 := by
  induction n with
  | zero => change (256*q+228)%4=0; omega
  | succ n ih => change (256*highJ3B q n+756)%4=0; omega

private theorem right3B_even (q d : Nat) : right3B q d%2=0 := by
  cases d with
  | zero => change (8160*q+7360)%2=0; omega
  | succ d => change (2*right3B q d+2)%2=0; omega

private theorem right3B_lower (q d : Nat) : 7360≤right3B q d := by
  induction d with
  | zero => change 7360≤8160*q+7360; omega
  | succ d ih => change 7360≤2*right3B q d+2; omega

private theorem right3B_eight (q d : Nat) :
    right3B q (d+8)=256*right3B q d+510 := by
  have hd : d+8=d+1+1+1+1+1+1+1+1 := by omega
  rw [hd]
  simp only [right3B]
  omega

private theorem high3B_right_eq (q n : Nat) :
    right3B q (8*n+3)=255*highJ3B q n+754 := by
  induction n with
  | zero =>
      change 2*(2*(2*(8160*q+7360)+2)+2)+2=255*(256*q+228)+754
      omega
  | succ n ih =>
      have hd : 8*(n+1)+3=(8*n+3)+8 := by omega
      rw [hd,right3B_eight]
      change 256*right3B q (8*n+3)+510=255*(256*highJ3B q n+756)+754
      rw [ih]
      omega

theorem high3B_right_tower (q n : Nat) :
    right3B q (8*n+3)=255*highJ3B q n+754 := high3B_right_eq q n

private theorem right3B_depth (q d : Nat) :
    BB6.Agent15.oddDepth (right3B q d)=d := by
  induction d with
  | zero =>
      have hn : ¬(4≤8160*q+7360 ∧ (8160*q+7360)%4=2) := by omega
      change BB6.Agent15.oddDepth (8160*q+7360)=0
      rw [BB6.Agent15.oddDepth,dif_neg hn]
  | succ d ih =>
      have he := right3B_even q d
      have hl := right3B_lower q d
      have hg : 4≤right3B q (d+1) ∧ right3B q (d+1)%4=2 := by
        simp only [right3B]
        omega
      have hr : (right3B q (d+1)-2)/2=right3B q d := by
        simp only [right3B]
        omega
      rw [BB6.Agent15.oddDepth,dif_pos hg,hr,ih]
      omega

private theorem right3B_terminal (q d a : Nat) (ha : a%4=3) :
    (BB6.Agent15.affineNormalize a (right3B q d)).2=8160*q+7360 := by
  induction d generalizing a with
  | zero =>
      have hn : ¬(4≤8160*q+7360 ∧ (8160*q+7360)%2=0 ∧
        (a+(8160*q+7360))%4=1) := by omega
      change (BB6.Agent15.affineNormalize a (8160*q+7360)).2=8160*q+7360
      rw [BB6.Agent15.affineNormalize,dif_neg hn]
  | succ d ih =>
      have he := right3B_even q d
      have hl := right3B_lower q d
      have hg : 4≤right3B q (d+1) ∧
          right3B q (d+1)%2=0 ∧
          (a+right3B q (d+1))%4=1 := by
        simp only [right3B]
        omega
      have ha' : (a+right3B q (d+1)-2)%4=3 := by
        simp only [right3B]
        omega
      have hr : (right3B q (d+1)-2)/2=right3B q d := by
        simp only [right3B]
        omega
      rw [BB6.Agent15.affineNormalize,dif_pos hg,hr]
      exact ih (a+right3B q (d+1)-2) ha'

theorem high3B_halt_input (q n : Nat) :
    secNext (2*highJ3B q n+3,255*highJ3B q n+754)=none := by
  apply (BB6.Agent15.section_halts_iff_parametric _ _).mpr
  right
  right
  refine ⟨highJ3B q n,3,by omega,?_⟩
  change (255*highJ3B q n+754)+highJ3B q n+3*3+5=256*(highJ3B q n+3)
  omega

theorem high3B_exact_depth (q n : Nat) :
    BB6.Agent15.oddDepth (255*highJ3B q n+754)=8*n+3 := by
  rw [←high3B_right_eq q n]
  exact right3B_depth q (8*n+3)

theorem high3B_normalized_cone (q n : Nat) :
    let p := BB6.Agent15.affineNormalize
      (2*highJ3B q n+3) (255*highJ3B q n+754)
    p.1%16=11 ∧ p.2%32=0 ∧ 32≤p.2 := by
  have hj := highJ3B_mod4 q n
  have ha : (2*highJ3B q n+3)%4=3 := by omega
  have hright : (BB6.Agent15.affineNormalize
      (2*highJ3B q n+3) (255*highJ3B q n+754)).2=8160*q+7360 := by
    rw [←high3B_right_eq q n]
    exact right3B_terminal q (8*n+3) (2*highJ3B q n+3) ha
  have hdepth := high3B_exact_depth q n
  have hmass := (BB6.Agent15.normalize_three_depth_invariants
    (2*highJ3B q n+3) (255*highJ3B q n+754) ha).1
  have heq : (BB6.Agent15.affineNormalize
    (2*highJ3B q n+3) (255*highJ3B q n+754)).1+2*(8160*q+7360)+4*(8*n+3)=
    (2*highJ3B q n+3)+2*(255*highJ3B q n+754) := by
    simpa only [hright,hdepth] using hmass
  dsimp
  omega

theorem high3B_blank_unreachable (q n : Nat) :
    ¬ BB6.Agent15.CReach (2*highJ3B q n+3) (255*highJ3B q n+754) := by
  intro hr
  have hnorm := (BB6.Agent15.reach_iff_normalize
    (2*highJ3B q n+3) (255*highJ3B q n+754)).mp hr
  obtain ⟨time,ht⟩ := hnorm
  have hc := high3B_normalized_cone q n
  let p := BB6.Agent15.affineNormalize
    (2*highJ3B q n+3) (255*highJ3B q n+754)
  let u := p.1/16
  let v := (p.2-32)/32
  have hc1 : p.1%16=11 := hc.1
  have hc2 : p.2%32=0 := hc.2.1
  have hc3 : 32≤p.2 := hc.2.2
  have hx : p.1=16*u+11 := by dsimp [u]; omega
  have hy : p.2=32*v+32 := by dsimp [v]; omega
  rw [hx,hy] at ht
  exact even_child_B_unreachable u v time ht

theorem high3B_power_identity (q n : Nat) :
    255*highJ3B q n+756=256^n*(65280*q+58896) := by
  induction n with
  | zero =>
      change 255*(256*q+228)+756=256^0*(65280*q+58896)
      omega
  | succ n ih =>
      calc
        255*highJ3B q (n+1)+756 = 256*(255*highJ3B q n+756) := by
          change 255*(256*highJ3B q n+756)+756=256*(255*highJ3B q n+756)
          omega
        _ = 256*(256^n*(65280*q+58896)) := by rw [ih]
        _ = 256^(n+1)*(65280*q+58896) := by
          simp only [Nat.pow_succ]
          ac_rfl

#print axioms high3B_halt_input
#print axioms high3B_exact_depth
#print axioms high3B_normalized_cone
#print axioms high3B_blank_unreachable
#print axioms high3B_power_identity
end BB6.Agent3
