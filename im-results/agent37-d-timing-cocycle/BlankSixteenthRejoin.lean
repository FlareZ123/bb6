import Lean.Elab.Tactic.Omega
import BlankFifteenthRejoin

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2SixteenthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def seed16 : DRegular.L :=
  ⟨64*BB6.Agent2FifteenthRoot.t15+33,1,5⟩

def terminal2077 : DRegular.L :=
  (DRegular.run 2077 seed16).getD ⟨9,0,0⟩

def t16 : Nat := (terminal2077.a-4)/9

/-- Exact DRegular computation after the fifteenth E/B reentry. -/
theorem terminal2077_exact :
    DRegular.run 2077 seed16 = some ⟨9*t16+4,5,1⟩ := by decide

def exception16Time : Nat :=
  BB6.Agent2FifteenthRoot.reentry15Time +
    DRegular.accumulated 2077 seed16

theorem blank_sixteenth_exception :
    ObsEq (run exception16Time blank)
      (DRegularSource.sourceSection ⟨9*t16+4,5,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    BB6.Agent2FifteenthRoot.reentry15Time
    2077 seed16 ⟨9*t16+4,5,1⟩
  · constructor
    · change 64*BB6.Agent2FifteenthRoot.t15+33 ≥ 2
      omega
    · left
      change (1:Nat) ≠ 0
      omega
  · exact terminal2077_exact
  · exact BB6.Agent2FifteenthRoot.blank_fifteenth_reentry

def packet16Time : Nat :=
  BB6.Agent32EAll.duration (3*t16) 4 +
    BB6.Agent25BGeneral.bCost t16

def reentry16Time : Nat := exception16Time+packet16Time

theorem blank_sixteenth_reentry :
    ObsEq (run reentry16Time blank)
      (DRegularSource.sourceSection ⟨64*t16+27,1,5⟩) := by
  exact source_chain exception16Time packet16Time blank
    (DRegularSource.sourceSection ⟨9*t16+4,5,1⟩)
    (DRegularSource.sourceSection ⟨64*t16+27,1,5⟩)
    blank_sixteenth_exception
    (by simpa only [packet16Time] using
      (BB6.Agent25BGeneral.exceptional_EB_general t16 3))

#print axioms terminal2077_exact
#print axioms blank_sixteenth_exception
#print axioms blank_sixteenth_reentry

end BB6.Agent2SixteenthRoot
