import Lean.Elab.Tactic.Omega
import BlankSixteenthRejoin
import SeventeenthTerminalCertificate
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2SeventeenthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def seed17 : DRegular.L :=
  BB6.Agent2SeventeenthArithmetic.seed17

def terminal2656 : DRegular.L :=
  BB6.Agent2SeventeenthArithmetic.terminal2656

def t17 : Nat :=
  BB6.Agent2SeventeenthArithmetic.t17

theorem terminal2656_exact :
    DRegular.run 2656 seed17 = some ⟨9 * t17 + 7, 7, 1⟩ := by
  simpa [seed17, t17] using
    BB6.Agent2SeventeenthArithmetic.terminal2656_exact

theorem t17_mod27 : t17 % 27 = 6 := by
  simpa [t17] using BB6.Agent2SeventeenthArithmetic.t17_mod27

def u17 : Nat := t17 / 3

theorem t17_eq_three_u17 : t17 = 3 * u17 := by
  have h := t17_mod27
  dsimp [u17]
  omega

def exception17Time : Nat :=
  BB6.Agent2SixteenthRoot.reentry16Time +
    DRegular.accumulated 2656 seed17

/-- Extend the authenticated sixteenth blank-root reentry through the
    exact 2,656-step regular excursion to the seventeenth E exceptional input. -/
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

#print axioms terminal2656_exact
#print axioms t17_mod27
#print axioms blank_seventeenth_exception

end BB6.Agent2SeventeenthRoot
