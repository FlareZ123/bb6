import CAllDepthBlank
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19M1
open BB6.Agent4Four
open BB6.Agent46

def ja (q : Nat) : Nat → Nat
  | 0 => 64*q+26
  | h+1 => 16*ja q h+42

def jb (q : Nat) : Nat → Nat
  | 0 => 256*q+266
  | h+1 => 16*jb q h+42

def sa (q : Nat) : Nat → Nat
  | 0 => 16*q+5
  | h+1 => 16*sa q h+30*h+31

def sb (q : Nat) : Nat → Nat
  | 0 => 64*q+64
  | h+1 => 16*sb q h+30*h+46

private theorem bandY_shift4 (r t : Nat) :
    bandY (r+4) t = 16*bandY r t+30 := by
  have hp : 1 ≤ (2:Nat)^r := Nat.pow_pos (by decide)
  have hp2 : 2 ≤ (2:Nat)^r*(16*t+44) := by
    have hm := Nat.mul_le_mul_right (16*t+44) hp
    omega
  have hpow : (2:Nat)^(r+4)*(16*t+44) =
      16*((2:Nat)^r*(16*t+44)) := by
    rw [Nat.pow_add]
    simp only [show (2:Nat)^4=16 by decide]
    ac_rfl
  dsimp [bandY]
  rw [hpow]
  omega

theorem a_y (q h : Nat) :
    15*ja q h+40 = bandY (4*h+2) (15*q+4) := by
  induction h with
  | zero =>
      simp [ja,bandY]
      omega
  | succ h ih =>
      have hr : 4*(h+1)+2=(4*h+2)+4 := by omega
      rw [hr, bandY_shift4]
      simp only [ja]
      omega

theorem b_y (q h : Nat) :
    15*jb q h+40 = bandY (4*h+4) (15*q+13) := by
  induction h with
  | zero =>
      simp [jb,bandY]
      omega
  | succ h ih =>
      have hr : 4*(h+1)+4=(4*h+4)+4 := by omega
      rw [hr, bandY_shift4]
      simp only [jb]
      omega

theorem a_x (q h : Nat) :
    2*ja q h+3 = 8*sa q h+7+4*(4*h+2) := by
  induction h with
  | zero =>
      simp [ja,sa]
      omega
  | succ h ih =>
      simp only [ja,sa]
      omega

theorem b_x (q h : Nat) :
    2*jb q h+3 = 8*sb q h+7+4*(4*h+4) := by
  induction h with
  | zero =>
      simp [jb,sb]
      omega
  | succ h ih =>
      simp only [jb,sb]
      omega

theorem ja_mod16 (q h : Nat) : ja q h % 16 = 10 := by
  induction h with
  | zero => simp [ja]; omega
  | succ h ih => simp only [ja]; omega

theorem jb_mod16 (q h : Nat) : jb q h % 16 = 10 := by
  induction h with
  | zero => simp [jb]; omega
  | succ h ih => simp only [jb]; omega

theorem ja_high_stop (q h : Nat) :
    (15*ja q h+40)+ja q h+3*1+5 =
      (2:Nat)^(2*1+2)*(ja q h+3) := by
  simp only [show (2:Nat)^(2*1+2)=16 by decide]
  omega

theorem jb_high_stop (q h : Nat) :
    (15*jb q h+40)+jb q h+3*1+5 =
      (2:Nat)^(2*1+2)*(jb q h+3) := by
  simp only [show (2:Nat)^(2*1+2)=16 by decide]
  omega

theorem ja_blank_unreachable (q h time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*ja q h+3,15*ja q h+40) := by
  rw [a_x q h, a_y q h]
  exact blank_excludes_all_depth_cylinders
    (4*h+2) (sa q h) (15*q+4) time

theorem jb_blank_unreachable (q h time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*jb q h+3,15*jb q h+40) := by
  rw [b_x q h, b_y q h]
  exact blank_excludes_all_depth_cylinders
    (4*h+4) (sb q h) (15*q+13) time

theorem ja_escapes_older_dyadic_gate (q h n : Nat) :
    ¬(n+4≤2*1+2 ∧
      (ja q h+3*1+3)%2^(n+4)=2^(n+2) ∧
      (2*ja q h+3)%8=(if n%2=0 then 7 else 3)) := by
  intro hg
  have hn : n=0 := by omega
  subst n
  simp only [show (2:Nat)^(0+4)=16 by decide,
    show (2:Nat)^(0+2)=4 by decide] at hg
  have hj := ja_mod16 q h
  omega

theorem jb_escapes_older_dyadic_gate (q h n : Nat) :
    ¬(n+4≤2*1+2 ∧
      (jb q h+3*1+3)%2^(n+4)=2^(n+2) ∧
      (2*jb q h+3)%8=(if n%2=0 then 7 else 3)) := by
  intro hg
  have hn : n=0 := by omega
  subst n
  simp only [show (2:Nat)^(0+4)=16 by decide,
    show (2:Nat)^(0+2)=4 by decide] at hg
  have hj := jb_mod16 q h
  omega

#print axioms a_y
#print axioms b_y
#print axioms a_x
#print axioms b_x
#print axioms ja_high_stop
#print axioms jb_high_stop
#print axioms ja_blank_unreachable
#print axioms jb_blank_unreachable
#print axioms ja_escapes_older_dyadic_gate
#print axioms jb_escapes_older_dyadic_gate
end BB6.Agent19M1
