import EvenChildSevenFour
import AffineParityDepth
import SectionParam
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Distinct authentic high stopping indices, beginning at 26 and
    increasing by a factor of sixteen each layer. -/
def highJ : Nat → Nat
  | 0 => 26
  | n+1 => 16*highJ n+42

/-- Exact iterated affine right-counter tower, beginning at 52. -/
def affineRight : Nat → Nat
  | 0 => 52
  | n+1 => 2*affineRight n+2

private theorem highJ_mod_four (n : Nat) : highJ n%4=2 := by
  induction n with
  | zero => decide
  | succ n ih =>
      change (16*highJ n+42)%4=2
      omega

private theorem right_even (d : Nat) : affineRight d%2=0 := by
  cases d with
  | zero => decide
  | succ d =>
      change (2*affineRight d+2)%2=0
      omega

private theorem right_four (d : Nat) :
    affineRight (d+4)=16*affineRight d+30 := by
  have hd : d+4=d+1+1+1+1 := by omega
  rw [hd]
  simp only [affineRight]
  omega

/-- The tower's right coordinate is the exact second stopping formula. -/
private theorem high_right_eq (n : Nat) :
    affineRight (4*n+3)=15*highJ n+40 := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hd : 4*(n+1)+3=(4*n+3)+4 := by omega
      rw [hd,right_four]
      change 16*affineRight (4*n+3)+30=15*(16*highJ n+42)+40
      rw [ih]
      omega

private theorem right_lower (d : Nat) : 52≤affineRight d := by
  induction d with
  | zero => decide
  | succ d ih =>
      change 52≤2*affineRight d+2
      omega

/-- The source-defined odd affine depth of the tower is exactly d. -/
private theorem right_depth (d : Nat) :
    BB6.Agent15.oddDepth (affineRight d)=d := by
  induction d with
  | zero =>
      have hn : ¬(4≤(52:Nat) ∧ 52%4=2) := by decide
      change BB6.Agent15.oddDepth 52=0
      rw [BB6.Agent15.oddDepth,dif_neg hn]
  | succ d ih =>
      have he := right_even d
      have hl := right_lower d
      have hg : 4≤affineRight (d+1) ∧ affineRight (d+1)%4=2 := by
        simp only [affineRight]
        omega
      have hr : (affineRight (d+1)-2)/2=affineRight d := by
        simp only [affineRight]
        omega
      rw [BB6.Agent15.oddDepth, dif_pos hg,hr,ih]
      omega

/-- For every d, the authentic section's unique affine normalization
    of any a=3 mod4 ends with right counter exactly 52. -/
private theorem right_terminal (d a : Nat) (ha : a%4=3) :
    (BB6.Agent15.affineNormalize a (affineRight d)).2=52 := by
  induction d generalizing a with
  | zero =>
      have hn : ¬(4≤(52:Nat) ∧ 52%2=0 ∧ (a+52)%4=1) := by omega
      change (BB6.Agent15.affineNormalize a 52).2=52
      rw [BB6.Agent15.affineNormalize,dif_neg hn]
  | succ d ih =>
      have he := right_even d
      have hl := right_lower d
      have hg : 4≤affineRight (d+1) ∧
          affineRight (d+1)%2=0 ∧
          (a+affineRight (d+1))%4=1 := by
        simp only [affineRight]
        omega
      have ha' : (a+affineRight (d+1)-2)%4=3 := by
        simp only [affineRight]
        omega
      have hr : (affineRight (d+1)-2)/2=affineRight d := by
        simp only [affineRight]
        omega
      rw [BB6.Agent15.affineNormalize,dif_pos hg,hr]
      exact ih (a+affineRight (d+1)-2) ha'

/-- Every index n is a genuine one-step halting source for Machine C.
    The stopping equation has m=1 and j=highJ n. -/
theorem high_tower_halt_input (n : Nat) :
    secNext (2*highJ n+3,15*highJ n+40)=none := by
  apply (BB6.Agent15.section_halts_iff_parametric _ _).mpr
  right
  right
  refine ⟨highJ n,1,by omega,?_⟩
  change (15*highJ n+40)+highJ n+3*1+5=16*(highJ n+3)
  omega

/-- Unbounded, exact original-source forced affine inverse depth. -/
theorem high_tower_exact_depth (n : Nat) :
    BB6.Agent15.oddDepth (15*highJ n+40)=4*n+3 := by
  rw [←high_right_eq n]
  exact right_depth (4*n+3)

/-- Every affine-normalized high tower state belongs to the
    source-exact seven-four cone of maximal incoming depth one. -/
theorem high_tower_normalized_cone (n : Nat) :
    let p := BB6.Agent15.affineNormalize (2*highJ n+3) (15*highJ n+40)
    p.1%8=7 ∧ p.2%8=4 ∧ 12≤p.2 := by
  have hj := highJ_mod_four n
  have ha : (2*highJ n+3)%4=3 := by omega
  have hright : (BB6.Agent15.affineNormalize
      (2*highJ n+3) (15*highJ n+40)).2=52 := by
    rw [←high_right_eq n]
    exact right_terminal (4*n+3) (2*highJ n+3) ha
  have hdepth := high_tower_exact_depth n
  have hmass := (BB6.Agent15.normalize_three_depth_invariants
    (2*highJ n+3) (15*highJ n+40) ha).1
  have heq : (BB6.Agent15.affineNormalize
      (2*highJ n+3) (15*highJ n+40)).1+2*52+4*(4*n+3)=
      (2*highJ n+3)+2*(15*highJ n+40) := by
    simpa only [hright,hdepth] using hmass
  dsimp
  omega

/-- Every authentic immediate stopping input in an unbounded inverse
    tower is absent from the true blank-start orbit at all times. -/
theorem high_tower_blank_unreachable (n : Nat) :
    ¬ BB6.Agent15.CReach (2*highJ n+3) (15*highJ n+40) := by
  intro hr
  have hnorm := (BB6.Agent15.reach_iff_normalize
    (2*highJ n+3) (15*highJ n+40)).mp hr
  obtain ⟨time,ht⟩ := hnorm
  have hc := high_tower_normalized_cone n
  exact (seven_four_blank_unreachable time _ _ hc.1 hc.2.1 hc.2.2) ht

/-- The stopping inputs form a genuinely infinite, strictly increasing
    family rather than a finite repetition. -/
theorem high_tower_strict_step (n : Nat) : highJ n<highJ (n+1) := by
  change highJ n<16*highJ n+42
  omega

#print axioms high_tower_halt_input
#print axioms high_tower_exact_depth
#print axioms high_tower_normalized_cone
#print axioms high_tower_blank_unreachable
#print axioms high_tower_strict_step

end BB6.Agent3
