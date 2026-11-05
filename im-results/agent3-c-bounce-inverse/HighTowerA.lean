import ChildATwoDepth
import HighTowerTwoParam
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Disjoint higher-stopping tower with 4n+4 forced affine inverse edges,
    whose normalizer falls in the sharp two-edge A rectangle. -/
def highJA (q : Nat) : Nat → Nat
  | 0 => 512*q+426
  | n+1 => 16*highJA q n+42

def rightA (q : Nat) : Nat → Nat
  | 0 => 480*q+400
  | d+1 => 2*rightA q d+2

private theorem highJA_mod4 (q n : Nat) : highJA q n%4=2 := by
  induction n with
  | zero => change (512*q+426)%4=2; omega
  | succ n ih => change (16*highJA q n+42)%4=2; omega

private theorem rightA_even (q d : Nat) : rightA q d%2=0 := by
  cases d with
  | zero => change (480*q+400)%2=0; omega
  | succ d => change (2*rightA q d+2)%2=0; omega

private theorem rightA_lower (q d : Nat) : 400≤rightA q d := by
  induction d with
  | zero => change 400≤480*q+400; omega
  | succ d ih => change 400≤2*rightA q d+2; omega

private theorem rightA_four (q d : Nat) :
    rightA q (d+4)=16*rightA q d+30 := by
  have hd : d+4=d+1+1+1+1 := by omega
  rw [hd]
  simp only [rightA]
  omega

private theorem highA_right_eq (q n : Nat) :
    rightA q (4*n+4)=15*highJA q n+40 := by
  induction n with
  | zero =>
      change 2*(2*(2*(2*(480*q+400)+2)+2)+2)+2=15*(512*q+426)+40
      omega
  | succ n ih =>
      have hd : 4*(n+1)+4=(4*n+4)+4 := by omega
      rw [hd,rightA_four]
      change 16*rightA q (4*n+4)+30=15*(16*highJA q n+42)+40
      rw [ih]
      omega

theorem highA_right_tower (q n : Nat) :
    rightA q (4*n+4)=15*highJA q n+40 := highA_right_eq q n

private theorem rightA_depth (q d : Nat) :
    BB6.Agent15.oddDepth (rightA q d)=d := by
  induction d with
  | zero =>
      have hn : ¬(4≤480*q+400 ∧ (480*q+400)%4=2) := by omega
      change BB6.Agent15.oddDepth (480*q+400)=0
      rw [BB6.Agent15.oddDepth,dif_neg hn]
  | succ d ih =>
      have he := rightA_even q d
      have hl := rightA_lower q d
      have hg : 4≤rightA q (d+1) ∧ rightA q (d+1)%4=2 := by
        simp only [rightA]
        omega
      have hr : (rightA q (d+1)-2)/2=rightA q d := by
        simp only [rightA]
        omega
      rw [BB6.Agent15.oddDepth,dif_pos hg,hr,ih]
      omega

private theorem rightA_terminal (q d a : Nat) (ha : a%4=3) :
    (BB6.Agent15.affineNormalize a (rightA q d)).2=480*q+400 := by
  induction d generalizing a with
  | zero =>
      have hn : ¬(4≤480*q+400 ∧ (480*q+400)%2=0 ∧
        (a+(480*q+400))%4=1) := by omega
      change (BB6.Agent15.affineNormalize a (480*q+400)).2=480*q+400
      rw [BB6.Agent15.affineNormalize,dif_neg hn]
  | succ d ih =>
      have he := rightA_even q d
      have hl := rightA_lower q d
      have hg : 4≤rightA q (d+1) ∧
          rightA q (d+1)%2=0 ∧
          (a+rightA q (d+1))%4=1 := by
        simp only [rightA]
        omega
      have ha' : (a+rightA q (d+1)-2)%4=3 := by
        simp only [rightA]
        omega
      have hr : (rightA q (d+1)-2)/2=rightA q d := by
        simp only [rightA]
        omega
      rw [BB6.Agent15.affineNormalize,dif_pos hg,hr]
      exact ih (a+rightA q (d+1)-2) ha'

theorem highA_halt_input (q n : Nat) :
    secNext (2*highJA q n+3,15*highJA q n+40)=none := by
  apply (BB6.Agent15.section_halts_iff_parametric _ _).mpr
  right
  right
  refine ⟨highJA q n,1,by omega,?_⟩
  change (15*highJA q n+40)+highJA q n+3*1+5=16*(highJA q n+3)
  omega

theorem highA_exact_depth (q n : Nat) :
    BB6.Agent15.oddDepth (15*highJA q n+40)=4*n+4 := by
  rw [←highA_right_eq q n]
  exact rightA_depth q (4*n+4)

theorem highA_normalized_cone (q n : Nat) :
    let p := BB6.Agent15.affineNormalize
      (2*highJA q n+3) (15*highJA q n+40)
    p.1%16=3 ∧ p.2%32=16 ∧ 16≤p.2 := by
  have hj := highJA_mod4 q n
  have ha : (2*highJA q n+3)%4=3 := by omega
  have hright : (BB6.Agent15.affineNormalize
      (2*highJA q n+3) (15*highJA q n+40)).2=480*q+400 := by
    rw [←highA_right_eq q n]
    exact rightA_terminal q (4*n+4) (2*highJA q n+3) ha
  have hdepth := highA_exact_depth q n
  have hmass := (BB6.Agent15.normalize_three_depth_invariants
    (2*highJA q n+3) (15*highJA q n+40) ha).1
  have heq : (BB6.Agent15.affineNormalize
    (2*highJA q n+3) (15*highJA q n+40)).1+2*(480*q+400)+4*(4*n+4)=
    (2*highJA q n+3)+2*(15*highJA q n+40) := by
    simpa only [hright,hdepth] using hmass
  dsimp
  omega

theorem highA_blank_unreachable (q n : Nat) :
    ¬ BB6.Agent15.CReach (2*highJA q n+3) (15*highJA q n+40) := by
  intro hr
  have hnorm := (BB6.Agent15.reach_iff_normalize
    (2*highJA q n+3) (15*highJA q n+40)).mp hr
  obtain ⟨time,ht⟩ := hnorm
  have hc := highA_normalized_cone q n
  let p := BB6.Agent15.affineNormalize
    (2*highJA q n+3) (15*highJA q n+40)
  let u := p.1/16
  let v := (p.2-16)/32
  have hc1 : p.1%16=3 := hc.1
  have hc2 : p.2%32=16 := hc.2.1
  have hx : p.1=16*u+3 := by dsimp [u]; omega
  have hy : p.2=32*v+16 := by dsimp [v]; omega
  rw [hx,hy] at ht
  exact even_child_A_unreachable u v time ht

theorem highA_power_identity (q n : Nat) :
    15*highJA q n+42=16^(n+1)*(480*q+402) := by
  induction n with
  | zero =>
      change 15*(512*q+426)+42=16^(0+1)*(480*q+402)
      simp only [show 16^(0+1)=16 by decide]
      omega
  | succ n ih =>
      calc
        15*highJA q (n+1)+42 = 16*(15*highJA q n+42) := by
          change 15*(16*highJA q n+42)+42 = 16*(15*highJA q n+42)
          omega
        _ = 16*(16^(n+1)*(480*q+402)) := by rw [ih]
        _ = 16^((n+1)+1)*(480*q+402) := by
          simp only [Nat.pow_succ]
          ac_rfl

#print axioms highA_halt_input
#print axioms highA_exact_depth
#print axioms highA_normalized_cone
#print axioms highA_blank_unreachable
#print axioms highA_power_identity
end BB6.Agent3
