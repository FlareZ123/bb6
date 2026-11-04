import Lean.Elab.Tactic.Omega
import SixthRejoin

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent35SeventhRoot
open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def w6 : Nat := BB6.Agent25SixthRoot.t6 / 27
def seed7 : DRegular.L :=
  ⟨8*(BB6.Agent35SixthRoot.kA w6)+17, 3, 2⟩

def terminal34 : DRegular.L :=
  (DRegular.run 34 seed7).getD ⟨9,0,0⟩
def t7 : Nat := (terminal34.a-4)/9

/-- The actual (very large) sixth-reentry unary parameter has this
    exact 34-return source-model continuation to the seventh E exception. -/
theorem terminal34_exact :
    DRegular.run 34 seed7 = some ⟨9*t7+4,3,1⟩ := by decide

def sixthReentryTime : Nat :=
  BB6.Agent25SixthRoot.nextRawTime +
    BB6.Agent35SixthRoot.costAll w6

theorem sixthReentry_original :
    ObsEq (run sixthReentryTime blank)
      (DRegularSource.sourceSection seed7) := by
  exact BB6.Agent35SixthRoot.blank_sixth_reentry

def seventhExceptionTime : Nat :=
  sixthReentryTime + DRegular.accumulated 34 seed7

/-- All 34 regular steps are transported from the real blank tape by
    the previously authenticated DRegular 11-case source contract. -/
theorem seventhException_original :
    ObsEq (run seventhExceptionTime blank)
      (DRegularSource.sourceSection ⟨9*t7+4,3,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    sixthReentryTime 34 seed7 ⟨9*t7+4,3,1⟩
  · constructor
    · change 8*(BB6.Agent35SixthRoot.kA w6)+17 ≥ 2
      omega
    · left
      change 3 ≠ 0
      omega
  · exact terminal34_exact
  · exact sixthReentry_original

def seventhReturnCost : Nat :=
  BB6.Agent32EAll.duration (3*t7) 2 +
    BB6.Agent25BGeneral.bCost t7

def seventhReentryTime : Nat :=
  seventhExceptionTime + seventhReturnCost

/-- The seventh original-blank E exception lies in the E/B regular
    rejoining cylinder, so the actual D-root trajectory survives beyond
    the sixth off-language episode and returns once more to L. -/
theorem seventhReentry_original :
    ObsEq (run seventhReentryTime blank)
      (DRegularSource.sourceSection ⟨64*t7+23,1,5⟩) := by
  exact source_chain seventhExceptionTime seventhReturnCost
    blank (DRegularSource.sourceSection ⟨9*t7+4,3,1⟩)
    (DRegularSource.sourceSection ⟨64*t7+23,1,5⟩)
    seventhException_original
    (BB6.Agent25BGeneral.exceptional_EB_general t7 1)

#print axioms terminal34_exact
#print axioms seventhException_original
#print axioms seventhReentry_original

end BB6.Agent35SeventhRoot
