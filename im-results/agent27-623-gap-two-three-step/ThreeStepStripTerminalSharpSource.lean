import ThreeStepStripSource

/-!
# Branch-faithful terminal-parent ratio-4 inequalities for #623

The authentic source distinguishes left terminal-parent sectors (where the
best error is 6n+44) from right sectors (whose even branch needs 9n+38).
This avoids putting the right-sector error on the first, left-oriented strip.
-/

namespace BB6.Agent27TerminalWindowSharpSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent49TerminalRatio4Source
open BB6.Agent27ThreeStepStripSource

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem ordinary_terminal_window_sharp (n x y aa dd : Nat)
    (hn : 10≤n) (hpos : 0<x) (hord : OrdinaryStep x y aa dd)
    (hy : y+3<3^(n+2))
    (hK : 2*(x+y+x+y+10+3*(n+2))+5<3^(n+5))
    (he : aa%2=0) (hh : highLevelNext (.D aa dd)=none) :
    (4*y≤x+6*n+44 ∧ x≤4*y+6*n+44) ∨
    (4*x≤y+9*n+38 ∧ y≤4*x+9*n+38) := by
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
      have hw := evenNear_terminal_ratio4_source x y p q r (n+2) (n+5) aa dd 1 5
        hpos h (by omega) (Or.inl rfl) (Or.inl rfl) hev hs he hh (by omega)
      right
      omega

#print axioms ordinary_terminal_window_sharp

end BB6.Agent27TerminalWindowSharpSource
