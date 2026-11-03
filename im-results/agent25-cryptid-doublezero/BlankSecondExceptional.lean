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

def terminal1026 : DRegular.L :=
  (DRegular.run 1026 firstReentry).getD ⟨9,0,0⟩
def secondT : Nat := (terminal1026.a - 10) / 9

theorem terminal1026_exact :
    DRegular.run 1026 firstReentry =
      some ⟨9*secondT+10,6,1⟩ := by decide

def secondExceptionTime : Nat :=
  firstReentryTime + DRegular.accumulated 1026 firstReentry

theorem secondException_original :
    ObsEq (run secondExceptionTime blank)
      (DRegularSource.sourceSection ⟨9*secondT+10,6,1⟩) := by
  have hc : DRegular.Canon firstReentry := by
    constructor
    · change 64*rootT+29 ≥ 2
      omega
    · left
      change 1 ≠ 0
      omega
  have ht : ObsEq
      (run (DRegular.accumulated 1026 firstReentry)
        (DRegularSource.sourceSection firstReentry))
      (DRegularSource.sourceSection ⟨9*secondT+10,6,1⟩) :=
    DRegular.transport_obs
      CryptidBoundary.run DRegularSource.sourceSection ObsEq
      (fun c => rfl) CryptidBoundary.run_add
      (fun c => cfgEq_refl (represent c))
      (fun x y z h g => cfgEq_trans h g)
      (fun n x y h => source_congr n h)
      BB6.ERemaining.source_contract
      1026 firstReentry ⟨9*secondT+10,6,1⟩
      hc terminal1026_exact
  exact source_chain firstReentryTime
    (DRegular.accumulated 1026 firstReentry)
    blank (DRegularSource.sourceSection firstReentry)
    (DRegularSource.sourceSection ⟨9*secondT+10,6,1⟩)
    firstReentry_original ht

