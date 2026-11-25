import Combined109Roster
import RootRaw10Core

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent13CrossRouteHeldLeaf109

open BB6Coverage
open BB6.Agent50TNFPilot
open BB6.Agent31FourHoleRoster
open BB6.Agent47Combined109

/-- This parent is not one of the fifteen already accepted whole-cylinder
    cuts (raw 66/70/80 and raw 86/87/88/91/92/93/97/98/100/101/102/104). -/
theorem firstOneB0_1LC_not_covered :
    BB6.Agent47Combined109.covered firstOneB0_1LC = false := by decide

/-- The B0=1LC parent is an actual member of the 109 residual roster,
    not an unrelated first-one branch. -/
theorem firstOneB0_1LC_in_reducedRoster :
    ∃ e ∈ BB6.Agent47Combined109.reducedRoster,
      BB6.Agent31FourHoleRoster.sameTable e.2 firstOneB0_1LC = true := by decide

/-- The roster entry is exactly this parent table, not merely a compatible
    intersection with it. -/
theorem firstOneB0_1LC_exact_member :
    ∃ e ∈ BB6.Agent47Combined109.reducedRoster,
      e.2 = firstOneB0_1LC := by
  obtain ⟨e, he, hsame⟩ := firstOneB0_1LC_in_reducedRoster
  exact ⟨e, he, BB6.Agent31FourHoleRoster.sameTable_sound hsame⟩

/-- Compatibility of two partial machines means their fixed transitions
    never disagree; an unassigned slot on either side is a wildcard. -/
def compatibleMachineB (p q : BB6Coverage.PartialMachine) : Bool :=
  (List.finRange 6).all fun state =>
    [false, true].all fun symbol =>
      decide (p (state, symbol) = none ∨ q (state, symbol) = none ∨
        p (state, symbol) = q (state, symbol))

/-- Packed side-witness table for the complete C1=0LA branch below
    the raw10 B0=1LC parent. Codes are the 1-based allMoves indices. -/
def c1_0laPacked :=
  BB6.Agent47SevenSideWitnesses.decodeRows
    [8, 0, 11, 0, 0, 1, 0, 0, 0, 0, 0, 0]

theorem c1_0la_hasWitness :
    BB6.Agent47SevenSideWitnesses.hasWitness c1_0laPacked = true := by decide

def c1_0laParent : BB6Coverage.PartialMachine :=
  BB6Coverage.refine firstOneB0_1LC
    (⟨2, by decide⟩, true)
    (some ⟨false, false, ⟨0, by decide⟩⟩)

theorem c1_0la_parent_matches :
    BB6.Agent31FourHoleRoster.sameTable
      (BB6.Agent50RootFrontier.unpackTable c1_0laPacked) c1_0laParent = true := by decide

/-- The entire C1=0LA child of raw10 is closed by one existing SideWitness
    cylinder, with no restriction on its remaining nine slots. -/
theorem c1_0la_parent_is_complete_side_witness :
    ∀ m, BB6Coverage.compatible c1_0laParent m →
      BB6.Agent13BlankDelay.WeightedBound 7014 m := by
  intro m hm
  have hEq :
      BB6.Agent50RootFrontier.unpackTable c1_0laPacked = c1_0laParent :=
    BB6.Agent31FourHoleRoster.sameTable_sound c1_0la_parent_matches
  have hm' : BB6Coverage.compatible
      (BB6.Agent50RootFrontier.unpackTable c1_0laPacked) m := by
    rw [hEq]
    exact hm
  exact BB6.Agent47SevenSideWitnesses.hasWitness_sound
    c1_0laPacked c1_0la_hasWitness m hm'

/-- The FARv3 held leaf is disjoint from every one of the 388 side-witness
    cylinders, so its 25 completions are genuinely additional. -/
theorem heldLeaf_disjoint_from_all_sideWitnesses :
    (BB6.Agent47SevenSideWitnesses.witnesses.all fun w =>
      !(compatibleMachineB (BB6.Agent50RootFrontier.unpackTable w.table)
        (toPartialMachine BB6CrossRouteHeldLeaf.heldTable))) = true := by decide

/-- The parent table in the 109 roster is exactly the parent used by the
    source-held leaf's finite-slot partition proof. -/
theorem rootResidual_matches_109_parent :
    BB6.Agent31FourHoleRoster.sameTable
      (toPartialMachine BB6CrossRouteHeldLeaf.rootResidual)
      firstOneB0_1LC = true := by decide

/-- The source-held leaf is a strict refinement of the actual 109 parent,
    in the roster's own PartialMachine encoding. -/
theorem heldTable_refines_109_parent :
    refinesMachine
      (toPartialMachine BB6CrossRouteHeldLeaf.heldTable)
      firstOneB0_1LC := by
  apply refinesMachineB_sound
  decide

/-- The parent identified by the source proof is the exact table in the
    109 roster; no text-only or hash-only matching is used. -/
theorem sourceHeldParent_is_exact_109_member :
    ∃ e ∈ BB6.Agent47Combined109.reducedRoster,
      BB6.Agent31FourHoleRoster.sameTable
        e.2 (toPartialMachine BB6CrossRouteHeldLeaf.rootResidual) = true := by
  obtain ⟨e, he, hsame⟩ := firstOneB0_1LC_in_reducedRoster
  have hparent :
      toPartialMachine BB6CrossRouteHeldLeaf.rootResidual = firstOneB0_1LC :=
    BB6.Agent31FourHoleRoster.sameTable_sound rootResidual_matches_109_parent
  refine ⟨e, he, ?_⟩
  rw [hparent]
  exact hsame

#print axioms firstOneB0_1LC_not_covered
#print axioms firstOneB0_1LC_in_reducedRoster
#print axioms firstOneB0_1LC_exact_member
#print axioms rootResidual_matches_109_parent
#print axioms heldTable_refines_109_parent
#print axioms sourceHeldParent_is_exact_109_member
#print axioms b0_1lcSideWitnesses_count
#print axioms b0_1lcSideWitnesses_safe
#print axioms heldLeaf_disjoint_from_all_sideWitnesses
#print axioms c1_0la_hasWitness
#print axioms c1_0la_parent_is_complete_side_witness

end BB6.Agent13CrossRouteHeldLeaf109
