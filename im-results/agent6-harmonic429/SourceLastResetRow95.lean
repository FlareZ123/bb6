import SourceMod16
import BB429LastResetRow95
import Lean.Elab.Tactic.Omega

namespace BB429SourceLastResetRow95

open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- Original-source transport of the eight refined branch-10 exclusions. -/
theorem branch10_not_9_5_lifts_source_unreachable (i n d x y : Nat)
    (hn : 18 ≤ n) (hd : 3 ≤ d) (hdx : d ≤ x)
    (hcase :
      (n%64=7 ∧ d%32=7) ∨
      (n%64=15 ∧ d%32=19) ∨
      (n%64=23 ∧ d%32=31) ∨
      (n%64=31 ∧ d%32=11) ∨
      (n%64=39 ∧ d%32=23) ∨
      (n%64=47 ∧ d%32=3) ∨
      (n%64=55 ∧ d%32=15) ∨
      (n%64=63 ∧ d%32=27))
    (hx : 4*x+3*n+21 = 2^(n+2)*(d+6)+2*d)
    (hy : y=2*(x-d)+1)
    (hsrc : BB429SourceLadder.sourceRun i highLevelStart = some (.J x y)) :
    False := by
  have hlocal := BB429SourceMod16.source_run_to_local i x y hsrc
  exact BB429LastResetRow95.branch10_not_9_5_lifts_unreachable
    n d x y hn hd hdx hcase hx hy ⟨i,hlocal⟩

#print axioms branch10_not_9_5_lifts_source_unreachable

/-- Original-source transport of the five refined row-13/1 exclusions. -/
theorem branch10_13_1_lifts_source_unreachable (i n d x y : Nat)
    (hn : 18 ≤ n) (hd : 3 ≤ d) (hdx : d ≤ x)
    (hcase :
      (n%64=35 ∧ d%32=25) ∨
      (n%64=3 ∧ d%32=9) ∨
      (n%64=11 ∧ d%32=21) ∨
      (n%64=19 ∧ d%32=1) ∨
      (n%64=27 ∧ d%32=13))
    (hx : 4*x+3*n+21 = 2^(n+2)*(d+6)+2*d)
    (hy : y=2*(x-d)+1)
    (hsrc : BB429SourceLadder.sourceRun i highLevelStart = some (.J x y)) :
    False := by
  have hlocal := BB429SourceMod16.source_run_to_local i x y hsrc
  exact BB429LastResetRow95.branch10_13_1_lifts_unreachable
    n d x y hn hd hdx hcase hx hy ⟨i,hlocal⟩

#print axioms branch10_13_1_lifts_source_unreachable


end BB429SourceLastResetRow95
