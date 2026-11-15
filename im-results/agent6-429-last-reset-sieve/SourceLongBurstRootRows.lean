import SourceLongBurstRootMod16
import LongBurstRootRows
import Lean.Elab.Tactic.Omega

namespace BB429SourceLongBurstRootRows

open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- Original-source version of the four branch-9 whole-class exclusions. -/
theorem branch9_bad_d_classes_source_unreachable (i n d x y : Nat)
    (hn : 18≤n) (hd : 4≤d) (hdx : d≤x)
    (hcase :
      (n%32=5 ∧ d%16=10) ∨
      (n%32=13 ∧ d%16=6) ∨
      (n%32=21 ∧ d%16=2) ∨
      (n%32=29 ∧ d%16=14))
    (hx : 4*x+3*n+25 = 2^(n+2)*(d+10)+2*d)
    (hy : y=2*(x-d)+1)
    (hsrc : BB429SourceBridge.sourceRun i (.J 0 0) = some (.J x y)) : False := by
  have hL : BB429SourceLadder.sourceRun i highLevelStart = some (.J x y) := by
    rw [← BB429SourceLongBurstRootMod16.lastReset_sourceRun_eq_sourceLadder]
    exact hsrc
  have hlocal := BB429SourceMod16.source_run_to_local i x y hL
  exact BB429LastResetOddRows.branch9_bad_d_classes_unreachable
    n d x y hn hd hdx hcase hx hy ⟨i,hlocal⟩

/-- Original-source version of the eight branch-10 whole-class exclusions. -/
theorem branch10_bad_d_classes_source_unreachable (i n d x y : Nat)
    (hn : 18≤n) (hd : 3≤d) (hdx : d≤x)
    (hcase :
      (n%32=3 ∧ d%16=5) ∨
      (n%32=7 ∧ d%16=11) ∨
      (n%32=11 ∧ d%16=1) ∨
      (n%32=15 ∧ d%16=7) ∨
      (n%32=19 ∧ d%16=13) ∨
      (n%32=23 ∧ d%16=3) ∨
      (n%32=27 ∧ d%16=9) ∨
      (n%32=31 ∧ d%16=15))
    (hx : 4*x+3*n+21 = 2^(n+2)*(d+6)+2*d)
    (hy : y=2*(x-d)+1)
    (hsrc : BB429SourceBridge.sourceRun i (.J 0 0) = some (.J x y)) : False := by
  have hL : BB429SourceLadder.sourceRun i highLevelStart = some (.J x y) := by
    rw [← BB429SourceLongBurstRootMod16.lastReset_sourceRun_eq_sourceLadder]
    exact hsrc
  have hlocal := BB429SourceMod16.source_run_to_local i x y hL
  exact BB429LastResetOddRows.branch10_bad_d_classes_unreachable
    n d x y hn hd hdx hcase hx hy ⟨i,hlocal⟩

/-- Original-source version of the eight rejected individual lifts. -/
theorem branch10_partial_lifts_source_unreachable (i n d x y : Nat)
    (hn : 18≤n) (hd : 3≤d) (hdx : d≤x)
    (hcase :
      (n%64=7 ∧ d%32=23) ∨
      (n%64=39 ∧ d%32=7) ∨
      (n%64=15 ∧ d%32=3) ∨
      (n%64=47 ∧ d%32=19) ∨
      (n%64=23 ∧ d%32=15) ∨
      (n%64=55 ∧ d%32=31) ∨
      (n%64=31 ∧ d%32=27) ∨
      (n%64=63 ∧ d%32=11))
    (hx : 4*x+3*n+21 = 2^(n+2)*(d+6)+2*d)
    (hy : y=2*(x-d)+1)
    (hsrc : BB429SourceBridge.sourceRun i (.J 0 0) = some (.J x y)) : False := by
  have hL : BB429SourceLadder.sourceRun i highLevelStart = some (.J x y) := by
    rw [← BB429SourceLongBurstRootMod16.lastReset_sourceRun_eq_sourceLadder]
    exact hsrc
  have hlocal := BB429SourceMod16.source_run_to_local i x y hL
  exact BB429LastResetOddRows.branch10_partial_lifts_unreachable
    n d x y hn hd hdx hcase hx hy ⟨i,hlocal⟩

#print axioms branch9_bad_d_classes_source_unreachable
#print axioms branch10_bad_d_classes_source_unreachable
#print axioms branch10_partial_lifts_source_unreachable

end BB429SourceLongBurstRootRows
