import DeepFourExclude
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29Depth
open BB6.Agent46

/-- Explicitly constructed second-family stopping-index progression.
    The first values are 10, 202, 3274, 52426, ... . -/
def secondOneJ : Nat → Nat
  | 0 => 10
  | n+1 => 16*secondOneJ n+42

/-- Exact affine-right tower with terminal value four. -/
def rightTower : Nat → Nat
  | 0 => 4
  | n+1 => 2*rightTower n+2

private theorem secondOneJ_mod_four (n : Nat) :
    secondOneJ n%4=2 := by
  induction n with
  | zero => decide
  | succ n ih =>
      change (16*secondOneJ n+42)%4=2
      omega

private theorem rightTower_even (n : Nat) :
    rightTower n%2=0 := by
  cases n with
  | zero => decide
  | succ n =>
      change (2*rightTower n+2)%2=0
      omega

private theorem rightTower_four (n : Nat) :
    rightTower (n+4)=16*rightTower n+30 := by
  have hi : n+4=n+1+1+1+1 := by omega
  rw [hi]
  simp only [rightTower]
  omega

private theorem secondOneJ_tower (n : Nat) :
    15*secondOneJ n+40=rightTower (4*n+5) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hi : 4*(n+1)+5=(4*n+5)+4 := by omega
      rw [hi,rightTower_four]
      change 15*(16*secondOneJ n+42)+40=
        16*rightTower (4*n+5)+30
      omega

/-- Every value in the exact right tower normalizes by true affine
    source predecessors to a terminal section whose right counter is
    four. No assumption on blank-origin reachability is made. -/
private theorem affine_right_tower_four (n x : Nat) (hx : x%4=3) :
    (BB6.Agent15.affineNormalize x (rightTower n)).2=4 := by
  induction n generalizing x with
  | zero =>
      have hn : ¬(4≤(4:Nat) ∧ 4%2=0 ∧ (x+4)%4=1) := by omega
      simp only [rightTower]
      rw [BB6.Agent15.affineNormalize,dif_neg hn]
  | succ n ih =>
      have he : rightTower n%2=0 := rightTower_even n
      have hgate : 4≤rightTower (n+1) ∧
          rightTower (n+1)%2=0 ∧
          (x+rightTower (n+1))%4=1 := by
        simp only [rightTower]
        omega
      have hnext : (x+rightTower (n+1)-2)%4=3 := by
        simp only [rightTower]
        omega
      have hright : (rightTower (n+1)-2)/2=rightTower n := by
        simp only [rightTower]
        omega
      rw [BB6.Agent15.affineNormalize,dif_pos hgate,hright]
      exact ih (x+rightTower (n+1)-2) hnext

/-- A true high-section stopping input for every index r, with
    second-family depth parameter m=1. -/
theorem second_one_family_stopping (r : Nat) :
    (15*secondOneJ r+40)+secondOneJ r+3*1+5=
      2^(2*1+2)*(secondOneJ r+3) := by
  norm_num
  omega

private theorem second_one_affine_right_four (r : Nat) :
    (BB6.Agent15.affineNormalize
      (2*secondOneJ r+3) (15*secondOneJ r+40)).2=4 := by
  have hj : (2*secondOneJ r+3)%4=3 := by
    have hh := secondOneJ_mod_four r
    omega
  rw [secondOneJ_tower]
  exact affine_right_tower_four (4*r+5) (2*secondOneJ r+3) hj

/-- UNBOUNDED, genuine blank-orbit exclusion: an infinite family of
    valid, distinct Machine C immediate stopping inputs is never
    reached by the authentic blank-start arithmetic section.
    First cases are (a,k)=(23,190), (407,3070), (6551,49150). -/
theorem second_one_family_unreachable (r : Nat) :
    ¬ BB6.Agent15.CReach
      (2*secondOneJ r+3) (15*secondOneJ r+40) := by
  have hj := secondOneJ_mod_four r
  exact second_deep_right_four_unreachable (secondOneJ r) 1
    (15*secondOneJ r+40)
    (second_one_family_stopping r)
    (by omega) (by decide) (by omega)
    (second_one_affine_right_four r)

/-- Strictly increasing indices make this a genuine infinite
    parameter family rather than a repetition of finitely many states. -/
private theorem second_one_strict_step (n : Nat) :
    secondOneJ n < secondOneJ (n+1) := by
  change secondOneJ n < 16*secondOneJ n+42
  omega

#print axioms second_one_family_stopping
#print axioms second_one_family_unreachable
#print axioms second_one_strict_step
end BB6.Agent29Depth
