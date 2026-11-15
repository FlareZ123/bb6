import BB429SourceBridge
import SourceMod16
import LongBurstRootMod16

namespace BB429SourceLongBurstRootMod16

open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- The last-reset sourceRun and SourceLadder's sourceRun are definitionally
    the same native accelerated iterate from the blank high-level state. -/
theorem lastReset_sourceRun_eq_sourceLadder (n : Nat) :
    BB429SourceBridge.sourceRun n (.J 0 0) =
      BB429SourceLadder.sourceRun n highLevelStart := by
  rfl

/-- Source-level version: a genuine original-source blank-root prestate
    cannot lie in any of the four branch-9 long-burst residue classes. -/
theorem branch9_bad_d_classes_source_unreachable (i n d x y : Nat)
    (hn : 18 ≤ n)
    (hcase :
      (n%32=1 ∧ d%16=12) ∨
      (n%32=9 ∧ d%16=8) ∨
      (n%32=17 ∧ d%16=4) ∨
      (n%32=25 ∧ d%16=0))
    (hdx : d ≤ x)
    (hx : 4*x + 3*n + 25 = 2^(n+2)*(d+10)+2*d)
    (hy : y = 2*(x-d)+1)
    (hsrc : BB429SourceBridge.sourceRun i (.J 0 0) =
      some (.J x y)) : False := by
  have hL : BB429SourceLadder.sourceRun i highLevelStart =
      some (.J x y) := by
    rw [← lastReset_sourceRun_eq_sourceLadder]
    exact hsrc
  have hlocal := BB429SourceMod16.source_run_to_local i x y hL
  exact BB429LastResetRootMod16.branch9_bad_d_classes_unreachable
    n d x y hn hcase hdx hx hy ⟨i,hlocal⟩

/-- The same source bridge transports the simple branch-8 exclusion. -/
theorem branch8_source_unreachable (i x y : Nat)
    (hx : x%2=0)
    (hy : y=1)
    (hsrc : BB429SourceBridge.sourceRun i (.J 0 0) =
      some (.J x y)) : False := by
  have hL : BB429SourceLadder.sourceRun i highLevelStart =
      some (.J x y) := by
    rw [← lastReset_sourceRun_eq_sourceLadder]
    exact hsrc
  have hlocal := BB429SourceMod16.source_run_to_local i x y hL
  exact BB429LastResetRootMod16.branch8_unreachable x y hx hy ⟨i,hlocal⟩

#print axioms lastReset_sourceRun_eq_sourceLadder
#print axioms branch9_bad_d_classes_source_unreachable
#print axioms branch8_source_unreachable

end BB429SourceLongBurstRootMod16
