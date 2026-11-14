import Lean.Elab.Tactic.Omega
import BlankSixteenthRejoin
import SeventeenthTerminalCertificate
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2SeventeenthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def exception17Time : Nat :=
  BB6.Agent2SixteenthRoot.reentry16Time +
    DRegular.accumulated 2656 seed17

theorem blank_seventeenth_exception :
    ObsEq (run exception17Time blank)
      (DRegularSource.sourceSection ⟨9 * t17 + 7, 7, 1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    BB6.Agent2SixteenthRoot.reentry16Time
    2656 seed17 ⟨9 * t17 + 7, 7, 1⟩
  · constructor
    · change 64 * BB6.Agent2SixteenthRoot.t16 + 27 ≥ 2
      omega
    · left
      change (1 : Nat) ≠ 0
      omega
  · exact terminal2656_exact
  · exact BB6.Agent2SixteenthRoot.blank_sixteenth_reentry

#print axioms blank_seventeenth_exception

end BB6.Agent2SeventeenthRoot
