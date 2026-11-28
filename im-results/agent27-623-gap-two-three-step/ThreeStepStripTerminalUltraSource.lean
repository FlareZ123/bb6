import ThreeStepStripTerminalSharpSource
import Agent22ExactDrainCocycleDepthSource
import Agent8LogConeSource

/-!
# Eliminating the even-near terminal-parent penalty under authentic mass

The source even-near terminal window previously had width 9n+38, unlike
the 6n+27 odd-near window, because its evaluator and B-drain were bounded
separately. At any genuine predecessor of an n>=10 root terminal chain the
parent mass is >=200n+600. Its right ratio-four window then forces the
first evaluator counter far above n+3. This activates the exact weighted
B-drain cocycle and restores a 6n+27 right terminal-parent window.

The mass hypothesis is explicit. No claim about arbitrary synthetic
terminal parents is made.
-/

namespace BB6.Agent27TerminalWindowUltraSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent49DrainLinearLogSource
open BB6.Agent49DrainLinearTerminalSource
open BB6.Agent49TerminalRatio4Source
open BB6.Agent22ExactDrainCocycleDepthSource
open BB6.Agent8LogConeSource
open BB6.Agent27ThreeStepStripSource

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem budget_at_depth (n a b : Nat)
    (ha : n+1≤a) (hb : b<3^n) : b≤ternaryOnes a := by
  have hmono := ternaryOnes_mono (n+1) a ha
  have hones := twice_ones_add_one_eq_pow (n+1)
  have hp : 3^(n+1)=3*3^n := by rw [Nat.pow_succ]; omega
  have hpos : 0<3^n := Nat.pow_pos (by decide)
  omega

private theorem weighted_at_depth (n a b d x y : Nat)
    (hb : b<3^n) (hbudget : b≤ternaryOnes a)
    (hs : drainB a b d=some (.D x y)) :
    ∃ r, r≤n ∧ x≤a+n ∧ a≤x+n+1 ∧
      2*x+y=2*a+d+3*b+2*r := by
  have hlo := drainB_first_lower_log n a b d x y hb hs
  have hhi := drainB_first_upper_log n a b d x y hb hs
  obtain ⟨r,hr,hpot⟩ :=
    drainB_weighted_depth n a b d x y hbudget hb hs
  exact ⟨r,hr,hhi,hlo,hpot⟩

theorem evenNear_terminal_window_ultra
    (n x y p q r aa dd : Nat)
    (hn : 10≤n) (hpos : 0<x) (hxy : x≤y)
    (hMass : 200*n+600≤x+y)
    (hy : y+3<3^(n+2))
    (hK : 2*(x+y+x+y+10+3*(n+2))+5<3^(n+5))
    (hEval : evalA (y+1-x) x (2*x+5)=some (p,q,r))
    (hDrain : drainB p q r=some (.D aa dd))
    (he : aa%2=0) (hhalt : highLevelNext (.D aa dd)=none) :
    4*x≤y+6*n+27 ∧ y≤4*x+6*n+27 := by
  have hWide := evenNear_terminal_ratio4_source
    x y p q r (n+2) (n+5) aa dd 1 5
    hpos hxy (by omega) (Or.inl rfl) (Or.inl rfl)
    hEval hDrain he hhalt (by omega)
  have hBigX : 20*n+100≤x := by omega
  have hFirst : n+3≤y+1-x := by omega
  have hb : x+1<3^(n+2) := by omega
  have hBudget := budget_at_depth (n+2) (y+1-x) (x+1) hFirst hb
  have hq : q≤x/3 :=
    evalA_second_le_quotient (y+1-x) x (2*x+5) p q r hEval
  have hqsmall : q<x+1 := by omega
  have hBundle : drainB (y+1-x) (x+1) 0 = some (.D aa dd) := by
    rw [drainB]
    have hne : x+1≠0 := by omega
    simp only [if_neg hne]
    have hindex : x+1-1=x := by omega
    have hthird : 0+2*(x+1)+3=2*x+5 := by omega
    rw [hindex,hthird,hEval]
    simp only [Option.bind_some,if_pos hqsmall]
    exact hDrain
  obtain ⟨rr,hrr,hup,hlo,hweight⟩ :=
    weighted_at_depth (n+2) (y+1-x) (x+1) 0 aa dd hb hBudget hBundle
  have hDaughterMass := evalA_drain_joint_mass
    (n+2) x y p q r aa dd hpos hxy (by omega) hEval hDrain
  have hbal := terminal_output_balance_of_mass aa dd (n+5)
    (y+2*x+5+3*(n+2)) hDaughterMass (by omega) he hhalt
  constructor <;> omega

/-- Terminal ratio-four window with the original-source left 6n+44 bound
and the restored even-right 6n+27 bound. -/
theorem ordinary_terminal_window_ultra (n x y aa dd : Nat)
    (hn : 10≤n) (hpos : 0<x) (hord : OrdinaryStep x y aa dd)
    (hMass : 200*n+600≤x+y)
    (hy : y+3<3^(n+2))
    (hK : 2*(x+y+x+y+10+3*(n+2))+5<3^(n+5))
    (he : aa%2=0) (hh : highLevelNext (.D aa dd)=none) :
    (4*y≤x+6*n+44 ∧ x≤4*y+6*n+44) ∨
    (4*x≤y+6*n+27 ∧ y≤4*x+6*n+27) := by
  cases hord with
  | oddFar h hs =>
      have hw := oddFar_terminal_ratio4_source x y (n+2) (n+5) aa dd 1 5
        h (Or.inl rfl) (Or.inl rfl) hs hy he hh (by omega)
      left
      omega
  | evenFar h hs =>
      have hw := evenFar_terminal_ratio4_source x y (n+2) (n+5) aa dd 1 5
        h (Or.inl rfl) (Or.inl rfl) hs (by omega) he hh (by omega)
      left
      omega
  | oddNear h hs =>
      have hw := oddNear_terminal_ratio4_source x y (n+2) (n+5) aa dd 1 5
        hpos h (Or.inl rfl) (Or.inl rfl) hs (by omega) he hh (by omega)
      right
      omega
  | evenNear p q r h hev hs =>
      right
      exact evenNear_terminal_window_ultra n x y p q r aa dd
        hn hpos h hMass hy hK hev hs he hh

#print axioms evenNear_terminal_window_ultra
#print axioms ordinary_terminal_window_ultra

end BB6.Agent27TerminalWindowUltraSource
