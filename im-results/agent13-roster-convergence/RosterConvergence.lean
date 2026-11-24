import FourHoleResidualRoster
import BlockPumpCoverage

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent13RosterConvergence

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent50RootFrontier
open BB6.Agent31FourHoleRoster
open BB6.Agent50RecursiveResidual

/-- First exceptional table from the generated nested-pump catalogue,
    with the Boolean parameter set to false. -/
def nestedFalse : PackedTable :=
  [ some (some ⟨true,true,1⟩),
    some (some ⟨false,false,2⟩),
    some (some ⟨true,true,2⟩),
    some (some ⟨true,false,5⟩),
    some (some ⟨false,true,3⟩),
    some (some ⟨true,true,1⟩),
    some (some ⟨true,false,3⟩),
    some (some ⟨true,true,4⟩),
    some (some ⟨false,true,5⟩),
    some (some ⟨false,false,1⟩),
    none,
    some (some ⟨false,false,0⟩) ]

/-- Second exceptional table from the generated nested-pump catalogue,
    with the Boolean parameter set to true. -/
def nestedTrue : PackedTable :=
  [ some (some ⟨true,true,1⟩),
    some (some ⟨false,false,2⟩),
    some (some ⟨true,true,2⟩),
    some (some ⟨true,false,5⟩),
    some (some ⟨false,true,3⟩),
    some (some ⟨true,true,1⟩),
    some (some ⟨true,false,3⟩),
    some (some ⟨true,true,4⟩),
    some (some ⟨true,true,0⟩),
    some (some ⟨false,false,1⟩),
    none,
    some (some ⟨false,false,0⟩) ]

/-- Third exceptional table from the generated two-block-growth catalogue. -/
def doubleGrow : PackedTable :=
  [ some (some ⟨true,true,1⟩),
    some (some ⟨true,false,0⟩),
    some (some ⟨true,true,2⟩),
    some (some ⟨true,false,5⟩),
    some (some ⟨false,true,3⟩),
    some (some ⟨true,true,2⟩),
    some (some ⟨true,false,3⟩),
    some (some ⟨true,true,4⟩),
    some (some ⟨false,false,4⟩),
    some (some ⟨false,false,1⟩),
    none,
    some (some ⟨false,false,0⟩) ]

/-- These are data exclusions only.  No exceptional-pump theorem is used
    in the convergence or soundness proofs below. -/
def exceptionalTables : List PackedTable :=
  [nestedFalse, nestedTrue, doubleGrow]

def exceptionalCovered (t : PackedTable) : Bool :=
  exceptionalTables.any (fun e => decide (e = t))

/-- Reconstruct the 124-table manifest without importing the current
    ExceptionalPumps proof module (whose never lemmas are not accepted). -/
def canonicalResidualRoster : List PackedTable :=
  pumpedRootRoster.filter (fun t => !exceptionalCovered t)

/-- Agent31's frontier, losslessly packed into the common twelve-slot
    representation used by the Agent50 recursive certificate. -/
def agent31PackedRoster : List PackedTable :=
  remainingRootRoster.map fun e => packTable e.2

/-- The two independently constructed residual frontiers are exactly the
    same finite set of partial transition tables.  This is checked by kernel
    computation over all twelve slots, not by hashes or cardinalities. -/
theorem agent31PackedRoster_perm_canonicalResidualRoster :
    List.Perm agent31PackedRoster canonicalResidualRoster := by
  decide

theorem canonicalResidualRoster_count :
    canonicalResidualRoster.length = 124 := by
  decide

/-- Transfer the sharper 395 weighted bound from the seven-edge proof to
    the canonical Agent50 roster.  The roster equality is the only bridge:
    no exceptional nonhalting claim is used. -/
theorem canonicalResidualRoster_sound_395 :
    ∀ m, compatible root m → WeightedBound 395 m ∨
      ∃ q ∈ canonicalResidualRoster, compatible (unpackTable q) m := by
  intro m hm
  rcases remainingRootRoster_sound m hm with hbound | ⟨e, he, hc⟩
  · exact Or.inl hbound
  · have hpack : packTable e.2 ∈ agent31PackedRoster := by
      exact List.mem_map.mpr ⟨e, he, rfl⟩
    have hclosed : packTable e.2 ∈ canonicalResidualRoster :=
      (List.Perm.mem_iff agent31PackedRoster_perm_canonicalResidualRoster).mp hpack
    exact Or.inr ⟨packTable e.2, hclosed, by
      simpa only [unpack_packTable] using hc⟩

#print axioms agent31PackedRoster_perm_canonicalResidualRoster
#print axioms canonicalResidualRoster_count
#print axioms canonicalResidualRoster_sound_395

end BB6.Agent13RosterConvergence
