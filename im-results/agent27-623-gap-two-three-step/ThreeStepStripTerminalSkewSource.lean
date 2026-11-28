import ThreeStepStripTerminalUltraSource
import DrainWeightedFirstCoupledSource
import ThreeStepStripWeightedSource

/-!
# One-sided terminal-parent ratio-four corridor at authentic root scale

At the high mass scale of a genuine third predecessor, the previously
proved symmetric terminal-parent bounds bootstrap a full ternary-ones
budget in all four ordinary sectors, including the composite even-near
evalA/drainB branch. The *same* outer drain count r then controls both
first-counter growth and weighted conservation. This yields one-sided
terminal-parent windows considerably sharper than the old symmetric 9n+38
bound. The root-scale mass hypothesis remains explicit.
-/

namespace BB6.Agent27TerminalSkewSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent49DrainLinearLogSource
open BB6.Agent49DrainLinearTerminalSource
open BB6.Agent49TerminalRatio4Source
open BB6.Agent22ExactDrainCocycleDepthSource
open BB6.Agent27ThreeStepStripSource
open BB6.Agent27ThreeStepWeightedSource
open BB6.Agent27TerminalWindowUltraSource
open BB6.Agent27DrainWeightedFirstCoupledSource

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem terminal_drain_coupled
    (n a b d aa dd : Nat)
    (ha : n+3≤a) (hb : b<3^(n+2))
    (hs : drainB a b d=some (.D aa dd))
    (he : aa%2=0) (hh : highLevelNext (.D aa dd)=none)
    (hK : 2*(a+d+3*b+3*(n+2)+1)+5<3^(n+5)) :
    ∃ r, r≤n+2 ∧ aa≤a+r ∧ a≤aa+n+3 ∧
      2*aa+dd=2*a+d+3*b+2*r ∧
      dd≤aa+n+9 ∧ aa≤dd+n+9 := by
  have hbudget := large_first_has_budget (n+2) a b ha hb
  obtain ⟨r,hr,hup,hEq⟩ :=
    drainB_weighted_depth_first_upper (n+2) a b d aa dd hbudget hb hs
  have hlo := drainB_first_lower_log (n+2) a b d aa dd hb hs
  have hbal := terminal_output_balance_joint a b d (n+2) (n+5)
    aa dd hs hb he hh hK
  exact ⟨r,hr,hup,(by omega),hEq,(by omega),(by omega)⟩

/-- Sector-sharp one-sided output corridors. The signs are essential:
left terminal x-4y has lower -2n-1, upper 6n+41;
right terminal y-4x has lower -2n-15, upper 6n+24. -/
theorem ordinary_terminal_window_skew (n x y aa dd : Nat)
    (hn : 10≤n) (hpos : 0<x) (hord : OrdinaryStep x y aa dd)
    (hMass : 200*n+600≤x+y)
    (hy : y+3<3^(n+2))
    (hK : 2*(x+y+x+y+10+3*(n+2))+5<3^(n+5))
    (he : aa%2=0) (hh : highLevelNext (.D aa dd)=none) :
    (x≤4*y+6*n+41 ∧ 4*y≤x+2*n+1) ∨
    (y≤4*x+6*n+24 ∧ 4*x≤y+2*n+15) := by
  cases hord with
  | oddFar h hs =>
      have hw := oddFar_terminal_ratio4_source x y (n+2) (n+5) aa dd 1 5
        h (Or.inl rfl) (Or.inl rfl) hs hy he hh (by omega)
      have ha : n+3≤x-y-5 := by omega
      have hK' : 2*((x-y-5)+5+3*(y+3)+3*(n+2)+1)+5<3^(n+5) := by omega
      obtain ⟨r,hr,hup,hlo,heq,hBal1,hBal2⟩ :=
        terminal_drain_coupled n (x-y-5) (y+3) 5 aa dd
          ha hy hs he hh hK'
      left
      constructor <;> omega
  | evenFar h hs =>
      have hw := evenFar_terminal_ratio4_source x y (n+2) (n+5) aa dd 1 5
        h (Or.inl rfl) (Or.inl rfl) hs (by omega) he hh (by omega)
      have hb : y+2<3^(n+2) := by omega
      have ha : n+3≤x-y-2 := by omega
      have hK' : 2*((x-y-2)+2+3*(y+2)+3*(n+2)+1)+5<3^(n+5) := by omega
      obtain ⟨r,hr,hup,hlo,heq,hBal1,hBal2⟩ :=
        terminal_drain_coupled n (x-y-2) (y+2) 2 aa dd
          ha hb hs he hh hK'
      left
      constructor <;> omega
  | oddNear h hs =>
      have hw := oddNear_terminal_ratio4_source x y (n+2) (n+5) aa dd 1 5
        hpos h (Or.inl rfl) (Or.inl rfl) hs (by omega) he hh (by omega)
      have hb : x-1<3^(n+2) := by omega
      have ha : n+3≤y+4-x := by omega
      have hK' : 2*((y+4-x)+3+3*(x-1)+3*(n+2)+1)+5<3^(n+5) := by omega
      obtain ⟨r,hr,hup,hlo,heq,hBal1,hBal2⟩ :=
        terminal_drain_coupled n (y+4-x) (x-1) 3 aa dd
          ha hb hs he hh hK'
      right
      constructor <;> omega
  | evenNear p q d h hev hs =>
      have hw := evenNear_terminal_ratio4_source
        x y p q d (n+2) (n+5) aa dd 1 5
        hpos h (by omega) (Or.inl rfl) (Or.inl rfl)
        hev hs he hh (by omega)
      have hb : x+1<3^(n+2) := by omega
      have ha : n+3≤y+1-x := by omega
      have hq : q≤x/3 :=
        evalA_second_le_quotient (y+1-x) x (2*x+5) p q d hev
      have hqsmall : q<x+1 := by omega
      have hbundle : drainB (y+1-x) (x+1) 0=some (.D aa dd) := by
        rw [drainB]
        have hne : x+1≠0 := by omega
        simp only [if_neg hne]
        have hindex : x+1-1=x := by omega
        have hthird : 0+2*(x+1)+3=2*x+5 := by omega
        rw [hindex,hthird,hev]
        simp only [Option.bind_some,if_pos hqsmall]
        exact hs
      have hK' : 2*((y+1-x)+0+3*(x+1)+3*(n+2)+1)+5<3^(n+5) := by omega
      obtain ⟨r,hr,hup,hlo,heq,hBal1,hBal2⟩ :=
        terminal_drain_coupled n (y+1-x) (x+1) 0 aa dd
          ha hb hbundle he hh hK'
      right
      constructor <;> omega

#print axioms ordinary_terminal_window_skew

end BB6.Agent27TerminalSkewSource
