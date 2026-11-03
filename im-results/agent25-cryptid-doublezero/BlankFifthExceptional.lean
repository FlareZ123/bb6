import Lean.Elab.Tactic.Omega
import BlankFourthExceptional

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000
namespace BB6.Agent25FifthRoot
open CryptidBoundary BB6.BoundaryPadding

def seed : DRegular.L := ⟨64*BB6.Agent25FourthRoot.t4+113,0,0⟩
def terminal4252 : DRegular.L :=
  (DRegular.run 4252 seed).getD ⟨9,0,0⟩
def t5 : Nat := terminal4252.a/9

theorem terminal4252_exact :
    DRegular.run 4252 seed = some ⟨9*t5+4,5,1⟩ := by decide

def fifthExceptionTime : Nat :=
  BB6.Agent25FourthRoot.fourthReentryTime + DRegular.accumulated 4252 seed

theorem fifthException_original :
    ObsEq (run fifthExceptionTime blank)
      (DRegularSource.sourceSection ⟨9*t5+4,5,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    BB6.Agent25FourthRoot.fourthReentryTime
    4252 seed ⟨9*t5+4,5,1⟩
  · constructor
    · change 64*BB6.Agent25FourthRoot.t4+113 ≥ 2
      omega
    · right
      rfl
  · exact terminal4252_exact
  · exact BB6.Agent25FourthRoot.fourthReentry_original

def bCost5 : Nat :=
  BB6.Agent32EAll.duration (3*t5) 4 +
    BB6.Agent25BGeneral.bCost t5
def fifthReentryTime : Nat := fifthExceptionTime+bCost5

theorem fifthReentry_original :
    ObsEq (run fifthReentryTime blank)
      (DRegularSource.sourceSection ⟨64*t5+27,1,5⟩) := by
  exact source_chain fifthExceptionTime bCost5 blank
    (DRegularSource.sourceSection ⟨9*t5+4,5,1⟩)
    (DRegularSource.sourceSection ⟨64*t5+27,1,5⟩)
    fifthException_original
    (by simpa only [show 64*t5+21+2*3=64*t5+27 by omega]
         using BB6.Agent25BGeneral.exceptional_EB_general t5 3)

#print axioms terminal4252_exact
#print axioms fifthException_original
#print axioms fifthReentry_original
end BB6.Agent25FifthRoot
