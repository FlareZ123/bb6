import Agent8RootCorridorSource
import Agent8LogParentSource
import Agent8RootCancellationBudgetInterfaces
import Agent49TerminalRatio4Source
import Agent49ParitySource
import Lean.Elab.Tactic.Omega

/-!
# Source-level exponent transfer for the rooted #623 terminal bridge

A hypothetical two-step terminal event puts its genuine blank-root parent in
the source angular corridor.  That corridor bounds the parent's total mass by
17 times its smaller coordinate plus 68.  Consequently, once that smaller
coordinate lies in its canonical ternary band with depth n >= 10, all four
terminal-ratio source branches receive their required drain-block and
mass-power budgets at depths n and n+6.

This module proves the exponent transfer only; it does not assume the
terminal ratio-four conclusion and does not yet close the finite small-depth
root prefix.
-/

namespace BB6.Agent8RootCancellationExponentTransfer

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent8RootCorridorSource
open BB6.Agent8LogParentSource
open BB6.Agent8RootCancellationBudgetInterfaces
open BB6.Agent49TerminalRatio4Source

/-- The exponential scale dominates the linear depth with ample slack. -/
theorem three_pow_dominates_linear (n : Nat) (hn : 10 <= n) :
    2*n+27 <= 3^n := by
  induction n, hn using Nat.le_induction with
  | base =>
      norm_num
  | succ n hn ih =>
      have hpow : 3^(n+1) = 3^n*3 := by simp [Nat.pow_succ]
      have hpos : 1 <= 3^n := by positivity
      omega

/-- The rooted angular corridor bounds the parent's mass in terms of its
smaller coordinate. -/
theorem corridor_parent_mass_bound (a d : Nat)
    (hodd : d%2=1 -> d<16*a ∧ a<16*d+68)
    (heven : d%2=0 -> d<14*a+24 ∧ a<16*d+44) :
    a+d <= 17*min a d+68 := by
  by_cases h : a<=d
  · rw [min_eq_left h]
    by_cases ho : d%2=1
    · have hd := (hodd ho).1
      omega
    · have he : d%2=0 := by omega
      have hd := (heven he).1
      omega
  · have hdle : d<=a := by omega
    rw [min_eq_right hdle]
    by_cases ho : d%2=1
    · have ha := (hodd ho).2
      omega
    · have he : d%2=0 := by omega
      have ha := (heven he).2
      omega

/-- Every canonical root parent in depth band n has enough source mass
budget for the terminal-ratio theorem at K=n+6.  The same estimate covers
both odd/even far-left and both near-right source branches. -/
theorem corridor_parent_power_budget (n a d : Nat)
    (hn : 10<=n)
    (hmax : min a d+3 < 3^n)
    (hodd : d%2=1 -> d<16*a ∧ a<16*d+68)
    (heven : d%2=0 -> d<14*a+24 ∧ a<16*d+44) :
    2*(a+2*d+10+3*n)+5 < 3^(n+6) ∧
    2*(a+2*d+7+3*n)+5 < 3^(n+6) ∧
    2*(d+2*a+5+3*n)+5 < 3^(n+6) := by
  have hmass := corridor_parent_mass_bound a d hodd heven
  have hm : min a d < 3^n := by omega
  have hlin := three_pow_dominates_linear n hn
  have hpos : 1 <= 3^n := by positivity
  have hmul : 68*min a d < 68*3^n := by
    exact Nat.mul_lt_mul_of_pos_left hm (by decide)
  have hsmall : 297+6*n <= 303*3^n := by omega
  have htotal : 68*min a d+297+6*n < 729*3^n := by omega
  have hpow : 3^(n+6) = 729*3^n := by
    calc
      3^(n+6) = 3^n*3^6 := by rw [Nat.pow_add]
      _ = 3^n*729 := by norm_num
      _ = 729*3^n := Nat.mul_comm _ _
  have htotal' : 68*min a d+297+6*n < 3^(n+6) := by
    rw [hpow]
    exact htotal
  have hfarOdd :
      2*(a+2*d+10+3*n)+5 <= 68*min a d+297+6*n := by
    omega
  have hfarEven :
      2*(a+2*d+7+3*n)+5 <= 68*min a d+297+6*n := by
    omega
  have hnear :
      2*(d+2*a+5+3*n)+5 <= 68*min a d+297+6*n := by
    omega
  exact ⟨lt_of_le_of_lt hfarOdd htotal',
    lt_of_le_of_lt hfarEven htotal',
    lt_of_le_of_lt hnear htotal'⟩

/-- In the odd far-left ray, the drain block count is below the canonical
ternary power. -/
theorem odd_far_block_budget (n a d : Nat)
    (hmax : min a d+3 < 3^n)
    (hfar : d+5<=a) :
    d+3 < 3^n := by
  have hm : min a d=d := min_eq_right (by omega)
  simpa [hm] using hmax

/-- In the odd near-right ray, the drain block count is below the canonical
ternary power. -/
theorem odd_near_block_budget (n a d : Nat)
    (hmax : min a d+3 < 3^n)
    (hnear : a<d+5) :
    a-1 < 3^n := by
  by_cases h : a<=d
  · have hm : min a d=a := min_eq_left h
    have hmax' : a+3<3^n := by simpa [hm] using hmax
    omega
  · have hd : d<=a := by omega
    have hm : min a d=d := min_eq_right hd
    have hmax' : d+3<3^n := by simpa [hm] using hmax
    omega

/-- In the even far-left ray, the drain block count is below the canonical
ternary power. -/
theorem even_far_block_budget (n a d : Nat)
    (hmax : min a d+3 < 3^n)
    (hfar : d+3<=a) :
    d+2 < 3^n := by
  have hm : min a d=d := min_eq_right (by omega)
  have hmax' : d+3<3^n := by simpa [hm] using hmax
  omega

/-- The exceptional even gap-two branch is already in the exact five-branch
gate budget once the parent lies in a depth-n band with n >= 10. -/
theorem even_gap_two_impossible (n a d : Nat)
    (hn : 10<=n)
    (hmin : 3^(n-1)-3 <= min a d)
    (hmax : min a d+3 < 3^n)
    (hno : ∀ k, ¬ gateBudget a d k)
    (hdEven : d%2=0)
    (hgap : a=d+2) :
    False := by
  have hm : min a d=d := by simp [hgap]
  have hminD : 3^(n-1)-3 <= d := by simpa [hm] using hmin
  have hmaxD : d+3 < 3^n := by simpa [hm] using hmax
  have hpowA : a < 3^(n+6) := by
    have hlt : a < 3^n := by omega
    have hmono : 3^n <= 3^(n+6) :=
      Nat.pow_le_pow_right (by decide : 0<3) (by omega)
    exact lt_of_lt_of_le hlt hmono
  have hlin := three_pow_dominates_linear n hn
  have hmul : 3*(3^(n-1)-3) <= 3*d := Nat.mul_le_mul_left 3 hminD
  have hpow : 3^n = 3^(n-1)*3 := by
    have hsucc : (n-1)+1=n := by omega
    rw [← hsucc, Nat.pow_succ]
  have hlow : 3^n <= 3*d+9 := by omega
  have hroom : 2*(n+6)+6 <= 3*a := by omega
  have hgate : gateBudget a d (n+6) := by
    unfold gateBudget
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hdEven,hgap,hpowA,hroom⟩)))
  exact hno (n+6) hgate

/-- Source-level exponent transfer for a genuine blank-root parent whose
daughter halts immediately.  The four surviving ray cases receive exactly
the block and mass bounds required by TerminalRatio4Source at depth n and
mass exponent n+6. -/
theorem blank_root_two_step_exponent_transfer
    (t a d aa dd n : Nat)
    (hseen : run t = some (.D a d))
    (hs : highLevelNext (.D a d) = some (.D aa dd))
    (hstop : highLevelNext (.D aa dd) = none)
    (hn : 10<=n)
    (hmin : 3^(n-1)-3 <= min a d)
    (hmax : min a d+3 < 3^n) :
    (d%2=1 ∧
      ((d+5<=a ∧ d+3<3^n ∧
          2*(a+2*d+10+3*n)+5 < 3^(n+6)) ∨
       (a<d+5 ∧ a-1<3^n ∧
          2*(d+2*a+5+3*n)+5 < 3^(n+6)))) ∨
    (d%2=0 ∧
      ((d+3<=a ∧ d+2<3^n ∧
          2*(a+2*d+7+3*n)+5 < 3^(n+6)) ∨
       (a<=d ∧ a<3^n ∧
          2*(d+2*a+5+3*n)+5 < 3^(n+6)))) := by
  have hc := blank_root_two_step_terminal_parent_corridor
    t a d aa dd hseen hs hstop
  rcases hc with ⟨haPos,hodd,heven,hno⟩
  have hbudget := corridor_parent_power_budget n a d hn hmax hodd heven
  rcases hbudget with ⟨hfarOdd,hfarEven,hnear⟩
  have haEven : a%2=0 := run_preserves_even t a d hseen
  by_cases hd : d%2=1
  · left
    refine ⟨hd, ?_⟩
    by_cases hfar : d+5<=a
    · left
      have hb := odd_far_block_budget n a d hmax hfar
      exact ⟨hfar,hb,hfarOdd⟩
    · right
      have hnear' : a<d+5 := by omega
      have hb := odd_near_block_budget n a d hmax hnear'
      exact ⟨hnear',hb,hnear⟩
  · have hdEven : d%2=0 := by omega
    right
    refine ⟨hdEven, ?_⟩
    by_cases hfar : d+3<=a
    · left
      have hb := even_far_block_budget n a d hmax hfar
      exact ⟨hfar,hb,hfarEven⟩
    · have hnear' : a<d+3 := by omega
      by_cases hgap : a=d+2
      · exact False.elim
          (even_gap_two_impossible n a d hn hmin hmax hno hdEven hgap)
      · right
        have haLeD : a<=d := by omega
        have hm : min a d=a := min_eq_left haLeD
        have hb : a<3^n := by
          have hmax' : a+3<3^n := by simpa [hm] using hmax
          omega
        exact ⟨haLeD,hb,hnear⟩

#print axioms three_pow_dominates_linear
#print axioms corridor_parent_mass_bound
#print axioms corridor_parent_power_budget
#print axioms odd_far_block_budget
#print axioms odd_near_block_budget
#print axioms even_far_block_budget
#print axioms even_gap_two_impossible
#print axioms blank_root_two_step_exponent_transfer

end BB6.Agent8RootCancellationExponentTransfer
