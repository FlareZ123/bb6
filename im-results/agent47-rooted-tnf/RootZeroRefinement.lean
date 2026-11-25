import FourHoleResidualRoster
import WeightedTNFCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47RootZero

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent31FourHoleFrontier
open BB6.Agent31FourHoleRoster
open BB6.Agent50TNFPilot

/-- The first residual sibling of the first-one root: after A0 = 1RB,
    choose B0 = 0LA. -/
def raw0Move : Move := ⟨false, false, 0⟩

def raw0Entry : Config := (knownRun BB6.Agent50TNFPilot.root 1).getD blank

theorem root_knownRun_one :
    knownRun BB6.Agent50TNFPilot.root 1 = some raw0Entry := by
  simp [raw0Entry, knownRun, knownStep, BB6.Agent50TNFPilot.root,
    blank, readSlot, applyMove]

theorem root_first_hole :
    BB6.Agent50TNFPilot.root (readSlot raw0Entry) = none := by
  decide

def raw0 : PartialMachine :=
  refine BB6.Agent50TNFPilot.root (readSlot raw0Entry) (some raw0Move)

theorem raw0_path : RawRootPath raw0 :=
  RawRootPath.step RawRootPath.root root_knownRun_one root_first_hole

/-- The raw0 cylinder reaches A1 after exactly two known steps. -/
def raw0AfterTwo : Config := (knownRun raw0 2).getD blank

theorem raw0_knownRun_two : knownRun raw0 2 = some raw0AfterTwo := by
  simp [raw0AfterTwo, knownRun, knownStep, raw0, raw0Move,
    raw0Entry, BB6.Agent50TNFPilot.root, refine, blank, readSlot, applyMove]

theorem raw0_second_hole : raw0 (readSlot raw0AfterTwo) = none := by
  decide

theorem raw0_halt_weight :
    ∀ d ∈ possibleDelays (refine raw0 (readSlot raw0AfterTwo) none) 0,
      d + 2 + 1 ≤ 7014 := by
  decide

def raw0Child (mv : Move) : PartialMachine :=
  refine raw0 (readSlot raw0AfterTwo) (some mv)

def raw0HaltChild : PartialMachine :=
  refine raw0 (readSlot raw0AfterTwo) none

theorem raw0Child_path (mv : Move) : RawRootPath (raw0Child mv) := by
  exact RawRootPath.step raw0_path raw0_knownRun_two raw0_second_hole

theorem raw0Child_root (mv : Move) :
    raw0Child mv initialSlot = some (some ⟨true, true, 1⟩) := by
  simp [raw0Child, raw0, refine, BB6.Agent50TNFPilot.root, initialSlot]

theorem raw0Child_noAssignedHalt (mv : Move) :
    weightedTNFNoAssignedHalt (raw0Child mv) := by
  have h0 : weightedTNFNoAssignedHalt raw0 :=
    weightedTNFNoAssignedHalt_refine BB6.Agent50TNFPilot.root
      (readSlot raw0Entry) raw0Move firstOneCylinder_no_assigned_halt
  exact weightedTNFNoAssignedHalt_refine raw0
    (readSlot raw0AfterTwo) mv h0

def move0RB : Move := ⟨false, true, 1⟩
def move1RB : Move := ⟨true, true, 1⟩
def move0LA : Move := ⟨false, false, 0⟩
def move0RA : Move := ⟨false, true, 0⟩
def move1RA : Move := ⟨true, true, 0⟩
def move0LB : Move := ⟨false, false, 1⟩
def move1LB : Move := ⟨true, false, 1⟩

/-- Seven ordinary A1 assignments close immediately: two exact lassos and
    five translation-periodic side cycles. -/
def raw0ClosedMoves : List Move :=
  [move0RB, move1RB, move0LA, move0RA, move1RA, move0LB, move1LB]

def raw0Witness (mv : Move) : ResidualNonhaltWitness :=
  if mv = move0RB then .lasso 4
  else if mv = move1RB then .lasso 3
  else if mv = move0LA then .side 2 3 false 0
  else if mv = move0RA then .side 2 3 true 0
  else if mv = move1RA then .side 2 3 true 0
  else if mv = move0LB then .side 2 4 false 0
  else .side 2 4 false 0

theorem raw0WitnessOK (mv : Move) (h : mv ∈ raw0ClosedMoves) :
    residualWitnessOK (raw0Child mv) (raw0Witness mv) = true := by
  simp [raw0ClosedMoves] at h
  rcases h with h | h | h | h | h | h | h
  all_goals subst mv <;> decide

theorem raw0ChildNever (mv : Move) (h : mv ∈ raw0ClosedMoves) :
    ∀ m, compatible (raw0Child mv) m → NeverHalts m :=
  residualWitnessOK_sound (raw0Child mv) (raw0Witness mv) (raw0WitnessOK mv h)

def raw0ClosedCertificate (mv : Move) (h : mv ∈ raw0ClosedMoves) :
    WeightedTNFCertificate 7014 (raw0Child mv) 6 :=
  WeightedTNFCertificate.nonhalt
    (raw0Child_root mv)
    (BB6.Agent50TNFPilot.support6 _)
    (raw0Child_noAssignedHalt mv)
    (raw0ChildNever mv h)

/-- The first-hole expansion of raw0 closes 7 ordinary children and the
    immediate-halt child, leaving exactly 17 ordinary child cylinders. -/
def raw0Frontier : RootedFrontier 7014 raw0 :=
  RootedFrontier.expand raw0_path raw0_knownRun_two raw0_second_hole
    raw0_halt_weight
    (fun mv =>
      if h : mv ∈ raw0ClosedMoves then
        RootedFrontier.closed (raw0Child_path mv) (raw0ClosedCertificate mv h)
      else
        RootedFrontier.residual (raw0Child_path mv))

def raw0Residuals : List (List Move × PartialMachine) :=
  RootedFrontier.residuals raw0Frontier

theorem raw0ClosedMoves_count : raw0ClosedMoves.length = 7 := by
  decide

theorem raw0Residuals_count : raw0Residuals.length = 17 := by
  decide

/-- Exact mass accounting for the A1 split: 7 nonhalting cylinders, one
    halting cylinder, and 17 unresolved cylinders, each with nine holes. -/
theorem raw0_mass_partition :
    raw0Residuals.length * 25^9 +
      raw0ClosedMoves.length * 25^9 + 25^9 = 25^10 := by
  rw [raw0Residuals_count, raw0ClosedMoves_count]
  norm_num [pow_succ]

/-- Every completion of raw0 is bounded by 7014 or lies in one of the
    seventeen explicit nine-hole residual cylinders. -/
theorem raw0Frontier_sound (m : Machine) (hm : compatible raw0 m) :
    WeightedBound 7014 m ∨
      ∃ e ∈ raw0Residuals, compatible e.2 m := by
  rcases RootedFrontier.sound raw0Frontier m hm with hBound |
    ⟨address, q, hopen, hq⟩
  · exact Or.inl hBound
  · exact Or.inr ⟨(address, q), OpenLeaf.mem_residuals hopen, hq⟩

#print axioms root_knownRun_one
#print axioms raw0_knownRun_two
#print axioms raw0ClosedMoves_count
#print axioms raw0Residuals_count
#print axioms raw0_mass_partition
#print axioms raw0Frontier_sound

end BB6.Agent47RootZero
