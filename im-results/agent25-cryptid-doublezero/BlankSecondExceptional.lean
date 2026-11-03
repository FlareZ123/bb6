import Lean.Elab.Tactic.Omega
import ExceptionalARejoin
import BlankAfterExceptionalRegular

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000
namespace BB6.Agent25SecondRoot
open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def terminal8394 : DRegular.L :=
  (DRegular.run 8394 BB6.BlankRegular8394.seed9).getD ⟨9,0,0⟩
def rootT : Nat := terminal8394.a / 9
def firstReentry : DRegular.L := ⟨64*rootT+29,1,5⟩
def firstEBCost : Nat :=
  BB6.Agent32EAll.duration (3*rootT) 5 + BB6.Agent25Rejoin.bCost rootT
def rootTime8394 : Nat :=
  36 + DRegular.accumulated 8394 BB6.BlankRegular8394.seed9
def firstReentryTime : Nat := rootTime8394 + firstEBCost

theorem terminal8394_exact :
    DRegular.run 8394 BB6.BlankRegular8394.seed9 =
      some ⟨9*rootT+4,6,1⟩ := by decide

theorem firstReentry_original :
    ObsEq (run firstReentryTime blank)
      (DRegularSource.sourceSection firstReentry) := by
  rcases BB6.BlankRegular8394.blank8394 with ⟨s,hs,hobs⟩
  rw [terminal8394_exact] at hs
  cases hs
  exact source_chain rootTime8394 firstEBCost blank
    (DRegularSource.sourceSection ⟨9*rootT+4,6,1⟩)
    (DRegularSource.sourceSection firstReentry)
    hobs (BB6.Agent25Rejoin.exceptional_EB_two_source rootT)

