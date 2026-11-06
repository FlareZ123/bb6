import Std

/-!
Source-definition-compatible arithmetic of Sheep generic first-even section
returns along a -2 dyadic corridor, plus the all-h modulo-five terminal gate.

Standalone: compiles under Lean 4.36.0-rc2 with ordinary axioms only.
This module does NOT import the original Cryptids machine or claim an
all-p, all-q source-connected diameter proof.
-/
namespace SheepCorridor

def genericFirst (a u : Nat) : Nat := 2^a*u + a + (u-1)/2

theorem forced_first (w : Nat) (hw : 1 ≤ w) :
    genericFirst 1 (4*w+3) = 10*w+8 := by
  unfold genericFirst
  simp only [Nat.pow_one]
  omega

theorem forced_first_even (w : Nat) (hw : 1 ≤ w) :
    genericFirst 1 (4*w+3) % 2 = 0 := by
  rw [forced_first w hw]
  omega

theorem forced_affine (w : Nat) (hw : 1 ≤ w) :
    4*(genericFirst 1 (4*w+3)+2) = 5*((8*w+6)+2) := by
  rw [forced_first w hw]
  omega

theorem residue_eight (x : Nat) (hx : x % 8 = 6) (hlarge : 14 ≤ x) :
    ∃ w : Nat, 1 ≤ w ∧ x = 8*w+6 := by
  refine ⟨x/8, ?_, ?_⟩ <;> omega

theorem forced_from_residue_eight (x : Nat) (hx : x%8=6) (hlarge : 14≤x) :
    ∃ w : Nat, 1≤w ∧ x=8*w+6 ∧
       genericFirst 1 (4*w+3) % 2 = 0 ∧
       4*(genericFirst 1 (4*w+3)+2) = 5*(x+2) := by
  obtain ⟨w,hw,hxw⟩ := residue_eight x hx hlarge
  refine ⟨w,hw,hxw,forced_first_even w hw,?_⟩
  rw [hxw]
  exact forced_affine w hw

theorem four_pow_mod_five (h : Nat) : 4^h % 5 = 1 ∨ 4^h % 5 = 4 := by
  induction h with
  | zero => simp
  | succ h ih =>
    rcases ih with h1 | h4
    · right
      rw [Nat.pow_succ, Nat.mul_mod, h1]
    · left
      rw [Nat.pow_succ, Nat.mul_mod, h4]

theorem forbidden_mod_five (h : Nat) : (1+2*4^h)%5 ≠ 1 := by
  rcases four_pow_mod_five h with h1 | h4
  · rw [Nat.add_mod, Nat.mul_mod, h1]
    decide
  · rw [Nat.add_mod, Nat.mul_mod, h4]
    decide

#print axioms forced_first
#print axioms forced_from_residue_eight
#print axioms forbidden_mod_five
end SheepCorridor
