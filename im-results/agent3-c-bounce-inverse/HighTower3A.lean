import ChildATwoDepth
import HighTowerTwoParam
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Disjoint higher-stopping tower with 8n+1 forced affine inverse edges,
    whose normalizer falls in the sharp two-edge A rectangle. -/
def highJ3A (q : Nat) : Nat → Nat
  | 0 => 64*q+16
  | n+1 => 256*highJ3A q n+756

def right3A (q : Nat) : Nat → Nat
  | 0 => 8160*q+2416
  | d+1 => 2*right3A q d+2

private theorem highJ3A_mod4 (q n : Nat) : highJ3A q n%4=0 := by
  induction n with
  | zero => change (64*q+16)%4=0; omega
  | succ n ih => change (256*highJ3A q n+756)%4=0; omega

private theorem right3A_even (q d : Nat) : right3A q d%2=0 := by
  cases d with
  | zero => change (8160*q+2416)%2=0; omega
  | succ d => change (2*right3A q d+2)%2=0; omega

private theorem right3A_lower (q d : Nat) : 2416≤right3A q d := by
  induction d with
  | zero => change 2416≤8160*q+2416; omega
  | succ d ih => change 2416≤2*right3A q d+2; omega

private theorem right3A_eight (q d : Nat) :
    right3A q (d+8)=256*right3A q d+510 := by
  have hd : d+8=d+1+1+1+1+1+1+1+1 := by omega
  rw [hd]
  simp only [right3A]
  omega

private theorem high3A_right_eq (q n : Nat) :
    right3A q (8*n+1)=255*highJ3A q n+754 := by
  induction n with
  | zero =>
      change 2*(8160*q+2416)+2=255*(64*q+16)+754
      omega
  | succ n ih =>
      have hd : 8*(n+1)+1=(8*n+1)+8 := by omega
      rw [hd,right3A_eight]
      change 256*right3A q (8*n+1)+510=255*(256*highJ3A q n+756)+754
      rw [ih]
      omega

theorem high3A_right_tower (q n : Nat) :
    right3A q (8*n+1)=255*highJ3A q n+754 := high3A_right_eq q n

private theorem right3A_depth (q d : Nat) :
    BB6.Agent15.oddDepth (right3A q d)=d := by
  induction d with
  | zero =>
      have hn : ¬(4≤8160*q+2416 ∧ (8160*q+2416)%4=2) := by omega
      change BB6.Agent15.oddDepth (8160*q+2416)=0
      rw [BB6.Agent15.oddDepth,dif_neg hn]
  | succ d ih =>
      have he := right3A_even q d
      have hl := right3A_lower q d
      have hg : 4≤right3A q (d+1) ∧ right3A q (d+1)%4=2 := by
        simp only [right3A]
        omega
      have hr : (right3A q (d+1)-2)/2=right3A q d := by
        simp only [right3A]
        omega
      rw [BB6.Agent15.oddDepth,dif_pos hg,hr,ih]
      omega

private theorem right3A_terminal (q d a : Nat) (ha : a%4=3) :
    (BB6.Agent15.affineNormalize a (right3A q d)).2=8160*q+2416 := by
  induction d generalizing a with
  | zero =>
      have hn : ¬(4≤8160*q+2416 ∧ (8160*q+2416)%2=0 ∧
        (a+(8160*q+2416))%4=1) := by omega
      change (BB6.Agent15.affineNormalize a (8160*q+2416)).2=8160*q+2416
      rw [BB6.Agent15.affineNormalize,dif_neg hn]
  | succ d ih =>
      have he := right3A_even q d
      have hl := right3A_lower q d
      have hg : 4≤right3A q (d+1) ∧
          right3A q (d+1)%2=0 ∧
          (a+right3A q (d+1))%4=1 := by
        simp only [right3A]
        omega
      have ha' : (a+right3A q (d+1)-2)%4=3 := by
        simp only [right3A]
        omega
      have hr : (right3A q (d+1)-2)/2=right3A q d := by
        simp only [right3A]
        omega
      rw [BB6.Agent15.affineNormalize,dif_pos hg,hr]
      exact ih (a+right3A q (d+1)-2) ha'

theorem high3A_halt_input (q n : Nat) :
    secNext (2*highJ3A q n+3,255*highJ3A q n+754)=none := by
  apply (BB6.Agent15.section_halts_iff_parametric _ _).mpr
  right
  right
  refine ⟨highJ3A q n,3,by omega,?_⟩
  change (255*highJ3A q n+754)+highJ3A q n+3*3+5=256*(highJ3A q n+3)
  omega

theorem high3A_exact_depth (q n : Nat) :
    BB6.Agent15.oddDepth (255*highJ3A q n+754)=8*n+1 := by
  rw [←high3A_right_eq q n]
  exact right3A_depth q (8*n+1)

theorem high3A_normalized_cone (q n : Nat) :
    let p := BB6.Agent15.affineNormalize
      (2*highJ3A q n+3) (255*highJ3A q n+754)
    p.1%16=3 ∧ p.2%32=16 ∧ 16≤p.2 := by
  have hj := highJ3A_mod4 q n
  have ha : (2*highJ3A q n+3)%4=3 := by omega
  have hright : (BB6.Agent15.affineNormalize
      (2*highJ3A q n+3) (255*highJ3A q n+754)).2=8160*q+2416 := by
    rw [←high3A_right_eq q n]
    exact right3A_terminal q (8*n+1) (2*highJ3A q n+3) ha
  have hdepth := high3A_exact_depth q n
  have hmass := (BB6.Agent15.normalize_three_depth_invariants
    (2*highJ3A q n+3) (255*highJ3A q n+754) ha).1
  have heq : (BB6.Agent15.affineNormalize
    (2*highJ3A q n+3) (255*highJ3A q n+754)).1+2*(8160*q+2416)+4*(8*n+1)=
    (2*highJ3A q n+3)+2*(255*highJ3A q n+754) := by
    simpa only [hright,hdepth] using hmass
  dsimp
  omega

theorem high3A_blank_unreachable (q n : Nat) :
    ¬ BB6.Agent15.CReach (2*highJ3A q n+3) (255*highJ3A q n+754) := by
  intro hr
  have hnorm := (BB6.Agent15.reach_iff_normalize
    (2*highJ3A q n+3) (255*highJ3A q n+754)).mp hr
  obtain ⟨time,ht⟩ := hnorm
  have hc := high3A_normalized_cone q n
  let p := BB6.Agent15.affineNormalize
    (2*highJ3A q n+3) (255*highJ3A q n+754)
  let u := p.1/16
  let v := (p.2-16)/32
  have hc1 : p.1%16=3 := hc.1
  have hc2 : p.2%32=16 := hc.2.1
  have hx : p.1=16*u+3 := by dsimp [u]; omega
  have hy : p.2=32*v+16 := by dsimp [v]; omega
  rw [hx,hy] at ht
  exact even_child_A_unreachable u v time ht

theorem high3A_power_identity (q n : Nat) :
    255*highJ3A q n+756=256^n*(16320*q+4836) := by
  induction n with
  | zero =>
      change 255*(64*q+16)+756=256^0*(16320*q+4836)
      omega
  | succ n ih =>
      calc
        255*highJ3A q (n+1)+756 = 256*(255*highJ3A q n+756) := by
          change 255*(256*highJ3A q n+756)+756=256*(255*highJ3A q n+756)
          omega
        _ = 256*(256^n*(16320*q+4836)) := by rw [ih]
        _ = 256^(n+1)*(16320*q+4836) := by
          simp only [Nat.pow_succ]
          ac_rfl

#print axioms high3A_halt_input
#print axioms high3A_exact_depth
#print axioms high3A_normalized_cone
#print axioms high3A_blank_unreachable
#print axioms high3A_power_identity
end BB6.Agent3
