import Lean.Elab.Tactic.Omega
import BlankFourteenthRejoin

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2FifteenthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def seed15 : DRegular.L :=
  ⟨64*BB6.Agent2FourteenthRoot.t14+27,1,5⟩

def terminal6821 : DRegular.L :=
  (DRegular.run 6821 seed15).getD ⟨9,0,0⟩

def t15 : Nat := (terminal6821.a-4)/9

/-- Exact DRegular computation after the fourteenth E/B reentry. -/
theorem terminal6821_exact :
    DRegular.run 6821 seed15 = some ⟨9*t15+4,8,1⟩ := by decide

def exception15Time : Nat :=
  BB6.Agent2FourteenthRoot.reentry14Time +
    DRegular.accumulated 6821 seed15

theorem blank_fifteenth_exception :
    ObsEq (run exception15Time blank)
      (DRegularSource.sourceSection ⟨9*t15+4,8,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    BB6.Agent2FourteenthRoot.reentry14Time
    6821 seed15 ⟨9*t15+4,8,1⟩
  · constructor
    · change 64*BB6.Agent2FourteenthRoot.t14+27 ≥ 2
      omega
    · left
      change (1:Nat) ≠ 0
      omega
  · exact terminal6821_exact
  · exact BB6.Agent2FourteenthRoot.blank_fourteenth_reentry

def packet15Time : Nat :=
  BB6.Agent32EAll.duration (3*t15) 7 +
    BB6.Agent25BGeneral.bCost t15

def reentry15Time : Nat := exception15Time+packet15Time

theorem blank_fifteenth_reentry :
    ObsEq (run reentry15Time blank)
      (DRegularSource.sourceSection ⟨64*t15+33,1,5⟩) := by
  exact source_chain exception15Time packet15Time blank
    (DRegularSource.sourceSection ⟨9*t15+4,8,1⟩)
    (DRegularSource.sourceSection ⟨64*t15+33,1,5⟩)
    blank_fifteenth_exception
    (by simpa only [packet15Time] using
      (BB6.Agent25BGeneral.exceptional_EB_general t15 6))

#print axioms terminal6821_exact
#print axioms blank_fifteenth_exception
#print axioms blank_fifteenth_reentry

end BB6.Agent2FifteenthRoot
