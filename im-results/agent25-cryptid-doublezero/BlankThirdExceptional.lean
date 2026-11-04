import Lean.Elab.Tactic.Omega
import OriginalRootChain

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000
namespace BB6.Agent25ThirdRoot
open CryptidBoundary BB6.BoundaryPadding

def seed : DRegular.L :=
  ⟨64*BB6.Agent25SecondRoot.secondT+97,0,0⟩
def terminal2665 : DRegular.L :=
  (DRegular.run 2665 seed).getD ⟨9,0,0⟩
def t3 : Nat := terminal2665.a/9

theorem terminal2665_exact :
    DRegular.run 2665 seed = some ⟨9*t3+4,8,1⟩ := by decide

def thirdExceptionTime : Nat :=
  BB6.Agent25SecondRoot.secondReentryTime + DRegular.accumulated 2665 seed

theorem thirdException_original :
    ObsEq (run thirdExceptionTime blank)
      (DRegularSource.sourceSection ⟨9*t3+4,8,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    BB6.Agent25SecondRoot.secondReentryTime
    2665 seed ⟨9*t3+4,8,1⟩
  · constructor
    · change 64*BB6.Agent25SecondRoot.secondT+97 ≥ 2
      omega
    · right
      rfl
  · exact terminal2665_exact
  · exact BB6.Agent25SecondRoot.secondReentry_original

def bCost3 : Nat :=
  BB6.Agent32EAll.duration (3*t3) 7 +
    BB6.Agent25BGeneral.bCost t3
def thirdReentryTime : Nat := thirdExceptionTime+bCost3

theorem thirdReentry_original :
    ObsEq (run thirdReentryTime blank)
      (DRegularSource.sourceSection ⟨64*t3+33,1,5⟩) := by
  exact source_chain thirdExceptionTime bCost3 blank
    (DRegularSource.sourceSection ⟨9*t3+4,8,1⟩)
    (DRegularSource.sourceSection ⟨64*t3+33,1,5⟩)
    thirdException_original
    (by simpa only [bCost3, show 64*t3+21+2*6=64*t3+33 by omega]
         using BB6.Agent25BGeneral.exceptional_EB_general t3 6)

#print axioms terminal2665_exact
#print axioms thirdException_original
#print axioms thirdReentry_original
end BB6.Agent25ThirdRoot
