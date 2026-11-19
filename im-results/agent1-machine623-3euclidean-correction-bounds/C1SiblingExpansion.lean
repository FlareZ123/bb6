import Machine623ParentAudit

namespace BB6Coverage

set_option maxRecDepth 15000
set_option maxHeartbeats 0

/-- The authentic depth-five child after the first four #623 reads and
    the actual D/1 instruction. -/
def agent1D1RootPrefix : PartialMachine :=
  machine623D1Child (machine623 machine623D1Slot)

/-- On that child, the next physical read is C/1 (at primitive time 9). -/
def agent1C1Slot : Slot := (⟨2, by decide⟩, true)

theorem agent1C1RootNextSlot :
    firstUnknownPhysical agent1D1RootPrefix 96 finiteBlank =
      some agent1C1Slot := by
  decide

theorem agent1C1Slot_unassigned :
    agent1D1RootPrefix agent1C1Slot = none :=
  firstUnknownPhysical_sound agent1D1RootPrefix 96 finiteBlank
    agent1C1Slot agent1C1RootNextSlot

/-- All 25 possible actions for one raw six-state input row:
    halt, then four write/direction choices for each next state. -/
def agent1AllTransitions : List (Option Move) :=
  none :: ((List.finRange 6).flatMap fun q =>
    [ some ⟨false, false, q⟩
    , some ⟨false, true, q⟩
    , some ⟨true, false, q⟩
    , some ⟨true, true, q⟩
    ])

theorem agent1AllTransitions_length :
    agent1AllTransitions.length = 25 := by
  decide

def agent1C1Child (t : Option Move) : PartialMachine :=
  refine agent1D1RootPrefix agent1C1Slot t

/-- Transition indices accepted by the existing source-sound finite
    halt/ray/zero-mask/lasso/entry-macro oracle. Index 0 is HALT;
    indices 1..24 enumerate the four ordinary actions for states A..F. -/
def agent1C1AcceptedIndices : List Nat :=
  List.filterMap
    (fun pair =>
      if lassoDecisionOracle (agent1C1Child pair.2) 6 6 12 2 4
      then some pair.1 else none)
    (List.zip (List.range 25) agent1AllTransitions)

#eval agent1C1AcceptedIndices

/-- One complete 25-way physical split at the next genuine read.  A
    child is certified only when the existing all-time source oracle
    returns true; all other children remain explicitly open. -/
def agent1C1SiblingAudit :
    FrontierAudit (DecidedBelow 6) agent1D1RootPrefix :=
  .branch agent1D1RootPrefix agent1C1Slot agent1C1Slot_unassigned
    (fun t _ =>
      if h : lassoDecisionOracle (agent1C1Child t) 6 6 12 2 4 = true then
        .certified (agent1C1Child t)
          (lassoDecisionOracle_sound (agent1C1Child t) 6 6 12 2 4 h)
      else
        .unresolved (agent1C1Child t))

#eval agent1C1SiblingAudit.report

theorem agent1C1SiblingAudit_exhaustive (m : Machine)
    (hm : compatible agent1D1RootPrefix m) :
    DecidedBelow 6 m ∨ agent1C1SiblingAudit.open m :=
  agent1C1SiblingAudit.exhaustive m hm

/-- The authentic #623 table follows the actual C/1 edge, whose bounded
    oracle still has no certificate; this split does not decide #623. -/
theorem agent1C1SiblingAudit_root_open :
    agent1C1SiblingAudit.open machine623 := by
  decide

#print axioms agent1C1RootNextSlot
#print axioms agent1AllTransitions_length
#print axioms agent1C1SiblingAudit_exhaustive
#print axioms agent1C1SiblingAudit_root_open

end BB6Coverage
