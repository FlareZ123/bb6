import SourceMod16
import BB429Forced13More
import BB429Forced15More

/-!
# Original Cryptids high-level source: new genuine-root 13/15 cylinders.

Both the machine's native highLevelNext and Agent5's local BB429.next
are bridged by BB429SourceLadder.source_step_eq and source_run_eq, so
the new reachability exclusions become theorems about the unchanged
Cryptids source. The source's raw-machine acceleration equivalence
is unchanged. This file is intended to compile in the pinned original
Cryptids lake project, not standalone outside that native environment.
-/

namespace BB429NativeCylinder
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- True original-source high-level runs on the 13 odd reset line have
    first-parameter residues confined to three of sixteen classes. -/
theorem original_source_branch13_mod16 (i q : Nat) (hq : 16 ≤ q)
    (hr : BB429SourceLadder.sourceRun i highLevelStart =
      some (.J (32*q+13) (64*q+23))) :
    q%16=4 ∨ q%16=12 ∨ q%16=13 := by
  have hl := BB429SourceMod16.source_run_to_local
    i (32*q+13) (64*q+23) hr
  exact BB429Forced13More.rooted_13_q_mod16 q hq ⟨i,hl⟩

/-- True original-source high-level runs on the 15 odd reset line
    exclude three of the eight parameter classes. -/
theorem original_source_branch15_mod8 (i q : Nat) (hq : 16 ≤ q)
    (hr : BB429SourceLadder.sourceRun i highLevelStart =
      some (.J (32*q+15) (64*q+27))) :
    q%8=0 ∨ q%8=3 ∨ q%8=4 ∨ q%8=6 ∨ q%8=7 := by
  have hl := BB429SourceMod16.source_run_to_local
    i (32*q+15) (64*q+27) hr
  exact BB429Forced15More.rooted_15_q_mod8_necessary q hq ⟨i,hl⟩

#print axioms original_source_branch13_mod16
#print axioms original_source_branch15_mod8
end BB429NativeCylinder
