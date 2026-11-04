import EvenChildSevenFour
import AffineParityDepth
import SectionParam
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

def highJ2 (q : Nat) : Nat → Nat
  | 0 => 64*q+26
  | n+1 => 16*highJ2 q n+42

def affineRight2 (q : Nat) : Nat → Nat
  | 0 => 120*q+52
  | d+1 => 2*affineRight2 q d+2

private theorem highJ2_mod_four (q n : Nat) : highJ2 q n%4=2 := by
  induction n with
  | zero =>
      change (64*q+26)%4=2
      omega
  | succ n ih =>
      change (16*highJ2 q n+42)%4=2
      omega

private theorem right2_even (q d : Nat) : affineRight2 q d%2=0 := by
  cases d with
  | zero =>
      change (120*q+52)%2=0
      omega
  | succ d =>
      change (2*affineRight2 q d+2)%2=0
      omega

private theorem right2_four (q d : Nat) :
    affineRight2 q (d+4)=16*affineRight2 q d+30 := by
  have hd : d+4=d+1+1+1+1 := by omega
  rw [hd]
  simp only [affineRight2]
  omega

private theorem high2_right_eq (q n : Nat) :
    affineRight2 q (4*n+3)=15*highJ2 q n+40 := by
  induction n with
  | zero =>
      change 2*(2*(2*(120*q+52)+2)+2)+2=15*(64*q+26)+40
      omega
  | succ n ih =>
      have hd : 4*(n+1)+3=(4*n+3)+4 := by omega
      rw [hd,right2_four]
      change 16*affineRight2 q (4*n+3)+30=15*(16*highJ2 q n+42)+40
      rw [ih]
      omega

private theorem right2_lower (q d : Nat) : 52≤affineRight2 q d := by
  induction d with
  | zero =>
      change 52≤120*q+52
      omega
  | succ d ih =>
      change 52≤2*affineRight2 q d+2
      omega

private theorem right2_depth (q d : Nat) :
    BB6.Agent15.oddDepth (affineRight2 q d)=d := by
  induction d with
  | zero =>
      have hn : ¬(4≤120*q+52 ∧ (120*q+52)%4=2) := by omega
      change BB6.Agent15.oddDepth (120*q+52)=0
      rw [BB6.Agent15.oddDepth,dif_neg hn]
  | succ d ih =>
      have he := right2_even q d
      have hl := right2_lower q d
      have hg : 4≤affineRight2 q (d+1) ∧
          affineRight2 q (d+1)%4=2 := by
        simp only [affineRight2]
        omega
      have hr : (affineRight2 q (d+1)-2)/2=affineRight2 q d := by
        simp only [affineRight2]
        omega
      rw [BB6.Agent15.oddDepth,dif_pos hg,hr,ih]
      omega

private theorem right2_terminal (q d a : Nat) (ha : a%4=3) :
    (BB6.Agent15.affineNormalize a (affineRight2 q d)).2=120*q+52 := by
  induction d generalizing a with
  | zero =>
      have hn : ¬(4≤120*q+52 ∧ (120*q+52)%2=0 ∧
          (a+(120*q+52))%4=1) := by omega
      change (BB6.Agent15.affineNormalize a (120*q+52)).2=120*q+52
      rw [BB6.Agent15.affineNormalize,dif_neg hn]
  | succ d ih =>
      have he := right2_even q d
      have hl := right2_lower q d
      have hg : 4≤affineRight2 q (d+1) ∧
          affineRight2 q (d+1)%2=0 ∧
          (a+affineRight2 q (d+1))%4=1 := by
        simp only [affineRight2]
        omega
      have ha' : (a+affineRight2 q (d+1)-2)%4=3 := by
        simp only [affineRight2]
        omega
      have hr : (affineRight2 q (d+1)-2)/2=affineRight2 q d := by
        simp only [affineRight2]
        omega
      rw [BB6.Agent15.affineNormalize,dif_pos hg,hr]
      exact ih (a+affineRight2 q (d+1)-2) ha'

/-- Every tower member satisfies the genuine Machine C immediate
    stopping equation with m=1. -/
theorem high2_halt_input (q n : Nat) :
    secNext (2*highJ2 q n+3,15*highJ2 q n+40)=none := by
  apply (BB6.Agent15.section_halts_iff_parametric _ _).mpr
  right
  right
  refine ⟨highJ2 q n,1,by omega,?_⟩
  change (15*highJ2 q n+40)+highJ2 q n+3*1+5=16*(highJ2 q n+3)
  omega

/-- The source-exact forced inverse depth is unbounded. -/
theorem high2_exact_depth (q n : Nat) :
    BB6.Agent15.oddDepth (15*highJ2 q n+40)=4*n+3 := by
  rw [←high2_right_eq q n]
  exact right2_depth q (4*n+3)

/-- Exact normalized pair, for all natural q and n. -/
theorem high2_normalized_exact (q n : Nat) :
    BB6.Agent15.affineNormalize (2*highJ2 q n+3) (15*highJ2 q n+40)=
    (32*highJ2 q n-(240*q+33+16*n),120*q+52) := by
  have hj := highJ2_mod_four q n
  have ha : (2*highJ2 q n+3)%4=3 := by omega
  have hright : (BB6.Agent15.affineNormalize
      (2*highJ2 q n+3) (15*highJ2 q n+40)).2=120*q+52 := by
    rw [←high2_right_eq q n]
    exact right2_terminal q (4*n+3) (2*highJ2 q n+3) ha
  have hdepth := high2_exact_depth q n
  have hmass := (BB6.Agent15.normalize_three_depth_invariants
    (2*highJ2 q n+3) (15*highJ2 q n+40) ha).1
  have heq : (BB6.Agent15.affineNormalize
      (2*highJ2 q n+3) (15*highJ2 q n+40)).1+2*(120*q+52)+4*(4*n+3)=
      (2*highJ2 q n+3)+2*(15*highJ2 q n+40) := by
    simpa only [hright,hdepth] using hmass
  apply Prod.ext
  · omega
  · exact hright

/-- The entire two-dimensional tower normalizes into the certified
    seven-four cone with maximum predecessor depth one. -/
theorem high2_normalized_cone (q n : Nat) :
    let p := BB6.Agent15.affineNormalize
      (2*highJ2 q n+3) (15*highJ2 q n+40)
    p.1%8=7 ∧ p.2%8=4 ∧ 12≤p.2 := by
  have hj := highJ2_mod_four q n
  have ha : (2*highJ2 q n+3)%4=3 := by omega
  have hright : (BB6.Agent15.affineNormalize
      (2*highJ2 q n+3) (15*highJ2 q n+40)).2=120*q+52 := by
    rw [←high2_right_eq q n]
    exact right2_terminal q (4*n+3) (2*highJ2 q n+3) ha
  have hdepth := high2_exact_depth q n
  have hmass := (BB6.Agent15.normalize_three_depth_invariants
    (2*highJ2 q n+3) (15*highJ2 q n+40) ha).1
  have heq : (BB6.Agent15.affineNormalize
      (2*highJ2 q n+3) (15*highJ2 q n+40)).1+2*(120*q+52)+4*(4*n+3)=
      (2*highJ2 q n+3)+2*(15*highJ2 q n+40) := by
    simpa only [hright,hdepth] using hmass
  dsimp
  omega

/-- Uniform nonreachability from the original blank section,
    at all times and for every pair of tower indices. -/
theorem high2_blank_unreachable (q n : Nat) :
    ¬ BB6.Agent15.CReach (2*highJ2 q n+3) (15*highJ2 q n+40) := by
  intro hr
  have hnorm := (BB6.Agent15.reach_iff_normalize
    (2*highJ2 q n+3) (15*highJ2 q n+40)).mp hr
  obtain ⟨time,ht⟩ := hnorm
  have hc := high2_normalized_cone q n
  exact (seven_four_blank_unreachable time _ _ hc.1 hc.2.1 hc.2.2) ht

theorem high2_strict_depth (q n : Nat) : highJ2 q n<highJ2 q (n+1) := by
  change highJ2 q n<16*highJ2 q n+42
  omega

theorem high2_strict_width (q n : Nat) : highJ2 q n<highJ2 (q+1) n := by
  induction n with
  | zero =>
      change 64*q+26<64*(q+1)+26
      omega
  | succ n ih =>
      change 16*highJ2 q n+42<16*highJ2 (q+1) n+42
      omega

#print axioms high2_halt_input
#print axioms high2_exact_depth
#print axioms high2_normalized_exact
#print axioms high2_normalized_cone
#print axioms high2_blank_unreachable
#print axioms high2_strict_width

end BB6.Agent3
