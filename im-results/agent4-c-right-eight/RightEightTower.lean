import RightEight
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4RightEight

/-- Positive affine two-counter right values 18,38,78,158,... . -/
def towerRight (n : Nat) : Nat := 10*2^(n+1)-2

private theorem tower_right_ge (n : Nat) : 18≤towerRight n := by
  unfold towerRight
  have h : 1≤2^n := Nat.pow_pos (by decide)
  rw [Nat.pow_succ]
  omega

private theorem tower_right_mod4 (n : Nat) : towerRight n%4=2 := by
  unfold towerRight
  rw [Nat.pow_succ]
  have hp : 0<2^n := Nat.pow_pos (by decide)
  omega

private theorem tower_right_step (n : Nat) :
    (towerRight (n+1)-2)/2=towerRight n := by
  unfold towerRight
  rw [show n+1+1=(n+1)+1 by omega,Nat.pow_succ,Nat.pow_succ]
  have hp : 0<2^n := Nat.pow_pos (by decide)
  omega

private theorem tower_right_next_delta (n : Nat) :
    (towerRight (n+1)-2)%8=4 := by
  unfold towerRight
  rw [show n+1+1=(n+1)+1 by omega,Nat.pow_succ,Nat.pow_succ]
  have hp : 0<2^n := Nat.pow_pos (by decide)
  omega

private theorem source_odd_right8 (a : Nat) (ha:a%8=3) :
    ¬ BB6.Agent15.CReach a 8 := by
  have heq : a=8*(a/8)+3 := by omega
  rw [heq]
  exact blank_no_three_eight (a/8)

private theorem tower_flip (n a : Nat)
    (ha : a%8 = if (n+1)%2=0 then 3 else 7) :
    (a+towerRight (n+1)-2)%8 = (if n%2=0 then 3 else 7) := by
  have hd := tower_right_next_delta n
  have hg := tower_right_ge (n+1)
  have hsum : (a+towerRight (n+1)-2)%8 = (a%8+4)%8 := by
    rw [show a+towerRight (n+1)-2=a+(towerRight (n+1)-2) by omega, Nat.add_mod,hd]
  by_cases he : n%2=0
  · have hn:(n+1)%2=1 := by omega
    simp [he,hn] at ha ⊢
    omega
  · have hn:(n+1)%2=0 := by omega
    have he1:n%2=1 := by omega
    simp [he1,hn] at ha ⊢
    omega

/-- An unbounded all-depth family of genuine Machine C blank-section
    exclusions. No finite depth bound and no synthetic-source assumption. -/
theorem blank_no_right_eight_tower (n a : Nat)
    (ha : a%8=(if n%2=0 then 3 else 7)) :
    ¬ BB6.Agent15.CReach a (towerRight n) := by
  induction n generalizing a with
  | zero =>
      have hright : towerRight 0=18 := by decide
      rw [hright]
      intro hr
      have hres0 : a%8=3 := by simpa using ha
      have hgate : (a+18)%4=1 := by omega
      have hp := (BB6.Agent15.blank_reach_iff_affine a 18
        (by decide) (by decide) hgate).mp hr
      have hparent : (a+18-2)%8=3 := by omega
      have he : (18-2)/2=8 := by decide
      rw [he] at hp
      exact source_odd_right8 (a+18-2) hparent hp
  | succ n ih =>
      intro hr
      have hkge := tower_right_ge (n+1)
      have hmod := tower_right_mod4 (n+1)
      have hgate : (a+towerRight (n+1))%4=1 := by
        have hres : a%8=(if (n+1)%2=0 then 3 else 7) := ha
        by_cases hpar : (n+1)%2=0
        · simp [hpar] at hres
          omega
        · simp [hpar] at hres
          omega
      have hp := (BB6.Agent15.blank_reach_iff_affine a (towerRight (n+1))
        (by omega) (by omega) hgate).mp hr
      have he : (towerRight (n+1)-2)/2=towerRight n := tower_right_step n
      rw [he] at hp
      have hres : a%8=(if (n+1)%2=0 then 3 else 7) := ha
      have hparent : (a+towerRight (n+1)-2)%8=(if n%2=0 then 3 else 7) :=
        tower_flip n a hres
      exact ih (a+towerRight (n+1)-2) hparent hp

#print axioms blank_no_right_eight_tower
end BB6.Agent4RightEight
