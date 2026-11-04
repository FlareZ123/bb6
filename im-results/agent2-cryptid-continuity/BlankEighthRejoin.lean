import Lean.Elab.Tactic.Omega
import SeventhRejoin

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2EighthRoot
open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def seed8 : DRegular.L :=
  ⟨64*BB6.Agent35SeventhRoot.t7+23,1,5⟩

def terminal6046 : DRegular.L :=
  (DRegular.run 6046 seed8).getD ⟨9,0,0⟩

def t8 : Nat := (terminal6046.a-10)/9

/-- Exact arithmetic of the genuine seed-9 orbit's eighth off-regular
    gateway, after the source-proved seventh exceptional reentry. -/
theorem terminal6046_exact :
    DRegular.run 6046 seed8 = some ⟨9*t8+10,3,1⟩ := by decide

def eighthExceptionTime : Nat :=
  BB6.Agent35SeventhRoot.seventhReentryTime +
    DRegular.accumulated 6046 seed8

/-- The eighth exceptional E input is an authentic blank-tape checkpoint,
    with an exact (symbolic) primitive-step time. -/
theorem eighthException_original :
    ObsEq (run eighthExceptionTime blank)
      (DRegularSource.sourceSection ⟨9*t8+10,3,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    BB6.Agent35SeventhRoot.seventhReentryTime
    6046 seed8 ⟨9*t8+10,3,1⟩
  · constructor
    · change 64*BB6.Agent35SeventhRoot.t7+23 ≥ 2
      omega
    · left
      change 1 ≠ 0
      omega
  · exact terminal6046_exact
  · exact BB6.Agent35SeventhRoot.seventhReentry_original

def eighthReturnCost : Nat :=
  BB6.Agent32EAll.duration (3*t8+2) 2 +
    BB6.Agent25AGeneral.aCost t8 0

def eighthReentryTime : Nat :=
  eighthExceptionTime + eighthReturnCost

/-- At the eighth exceptional episode, the genuine blank orbit rejoins
    a pure-unary physical F/0 section via the all-parameter E/A theorem. -/
theorem eighthReentry_original :
    ObsEq (run eighthReentryTime blank)
      (DRegularSource.sourceSection ⟨64*t8+81,0,0⟩) := by
  exact source_chain eighthExceptionTime eighthReturnCost
    blank (DRegularSource.sourceSection ⟨9*t8+10,3,1⟩)
    (DRegularSource.sourceSection ⟨64*t8+81,0,0⟩)
    eighthException_original
    (by simpa only [eighthReturnCost] using
      (BB6.Agent25AGeneral.exceptional_EA_general t8 0))

#print axioms terminal6046_exact
#print axioms eighthException_original
#print axioms eighthReentry_original
end BB6.Agent2EighthRoot
