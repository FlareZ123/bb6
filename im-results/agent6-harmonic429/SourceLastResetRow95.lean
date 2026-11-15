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

/-- Original-source transport of the sixteen row-13/1 exclusions. -/
theorem branch10_13_1_lifts_source_unreachable (i n d x y : Nat)
    (hn : 18 ≤ n) (hd : 3 ≤ d) (hdx : d ≤ x)
    (hcase :
      (n%128=3 ∧ d%64=41) ∨
      (n%128=11 ∧ d%64=53) ∨
      (n%128=19 ∧ d%64=1) ∨
      (n%128=27 ∧ d%64=13) ∨
      (n%128=35 ∧ d%64=25) ∨
      (n%128=43 ∧ d%64=37) ∨
      (n%128=51 ∧ d%64=49) ∨
      (n%128=59 ∧ d%64=61) ∨
      (n%128=67 ∧ d%64=9) ∨
      (n%128=75 ∧ d%64=21) ∨
      (n%128=83 ∧ d%64=33) ∨
      (n%128=91 ∧ d%64=45) ∨
      (n%128=99 ∧ d%64=57) ∨
      (n%128=107 ∧ d%64=5) ∨
      (n%128=115 ∧ d%64=17) ∨
      (n%128=123 ∧ d%64=29))
    (hx : 4*x+3*n+21 = 2^(n+2)*(d+6)+2*d)
    (hy : y=2*(x-d)+1)
    (hsrc : BB429SourceLadder.sourceRun i highLevelStart = some (.J x y)) :
    False := by
  have hlocal := BB429SourceMod16.source_run_to_local i x y hsrc
  exact BB429LastResetRow95.branch10_13_1_lifts_unreachable
    n d x y hn hd hdx hcase hx hy ⟨i,hlocal⟩

#print axioms branch10_13_1_lifts_source_unreachable

/-- Original-source transport of the sixteen row-5/1 exclusions. -/
theorem branch10_5_1_lifts_source_unreachable (i n d x y : Nat)
    (hn : 18 ≤ n) (hd : 3 ≤ d) (hdx : d ≤ x)
    (hcase :
      (n%128=3 ∧ d%64=25) ∨
      (n%128=11 ∧ d%64=37) ∨
      (n%128=19 ∧ d%64=49) ∨
      (n%128=27 ∧ d%64=61) ∨
      (n%128=35 ∧ d%64=9) ∨
      (n%128=43 ∧ d%64=21) ∨
      (n%128=51 ∧ d%64=33) ∨
      (n%128=59 ∧ d%64=45) ∨
      (n%128=67 ∧ d%64=57) ∨
      (n%128=75 ∧ d%64=5) ∨
      (n%128=83 ∧ d%64=17) ∨
      (n%128=91 ∧ d%64=29) ∨
      (n%128=99 ∧ d%64=41) ∨
      (n%128=107 ∧ d%64=53) ∨
      (n%128=115 ∧ d%64=1) ∨
      (n%128=123 ∧ d%64=13))
    (hx : 4*x+3*n+21 = 2^(n+2)*(d+6)+2*d)
    (hy : y=2*(x-d)+1)
    (hsrc : BB429SourceLadder.sourceRun i highLevelStart = some (.J x y)) :
    False := by
  have hlocal := BB429SourceMod16.source_run_to_local i x y hsrc
  exact BB429LastResetRow95.branch10_5_1_lifts_unreachable
    n d x y hn hd hdx hcase hx hy ⟨i,hlocal⟩

#print axioms branch10_5_1_lifts_source_unreachable



end BB429SourceLastResetRow95
