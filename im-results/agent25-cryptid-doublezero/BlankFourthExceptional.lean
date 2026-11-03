import Lean.Elab.Tactic.Omega
import BlankThirdExceptional

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000
namespace BB6.Agent25FourthRoot
open CryptidBoundary BB6.BoundaryPadding

def seed : DRegular.L := ⟨64*BB6.Agent25ThirdRoot.t3+33,1,5⟩
def terminal10946 : DRegular.L :=
  (DRegular.run 10946 seed).getD ⟨9,0,0⟩
def t4 : Nat := (terminal10946.a-10)/9

theorem terminal10946_exact :
    DRegular.run 10946 seed = some ⟨9*t4+10,9,1⟩ := by decide

def fourthExceptionTime : Nat :=
  BB6.Agent25ThirdRoot.thirdReentryTime + DRegular.accumulated 10946 seed

theorem fourthException_original :
    ObsEq (run fourthExceptionTime blank)
      (DRegularSource.sourceSection ⟨9*t4+10,9,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    BB6.Agent25ThirdRoot.thirdReentryTime
    10946 seed ⟨9*t4+10,9,1⟩
  · constructor
    · change 64*BB6.Agent25ThirdRoot.t3+33 ≥ 2
      omega
    · left
      change 1 ≠ 0
      omega
  · exact terminal10946_exact
  · exact BB6.Agent25ThirdRoot.thirdReentry_original

def aCost4 : Nat :=
  BB6.Agent32EAll.duration (3*t4+2) 8 +
    BB6.Agent25AGeneral.aCost t4 2
def fourthReentryTime : Nat := fourthExceptionTime+aCost4

theorem fourthReentry_original :
    ObsEq (run fourthReentryTime blank)
      (DRegularSource.sourceSection ⟨64*t4+113,0,0⟩) := by
  exact source_chain fourthExceptionTime aCost4 blank
    (DRegularSource.sourceSection ⟨9*t4+10,9,1⟩)
    (DRegularSource.sourceSection ⟨64*t4+113,0,0⟩)
    fourthException_original
    (by simpa only [show 64*t4+65+16*(2+1)=64*t4+113 by omega]
         using BB6.Agent25AGeneral.exceptional_EA_general t4 2)

#print axioms terminal10946_exact
#print axioms fourthException_original
#print axioms fourthReentry_original
end BB6.Agent25FourthRoot
