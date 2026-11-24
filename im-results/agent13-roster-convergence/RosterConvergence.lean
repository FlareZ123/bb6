import FourHoleResidualRoster
import PureFourHoleResiduals
import RecursiveResidual
import DepthEightSiblingData1
import DepthEightSiblingData2
import DepthEightSiblingData3
import DepthEightSiblingData4
import C1Growth
import BlockPumpData1
import BlockPumpData2
import BlockPumpData3
import BlockPumpData4

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent13RosterConvergence

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent50RootFrontier
open BB6.Agent31FourHoleRoster
open BB6.Agent50RecursiveResidual
open BB6Coverage.Agent50Pump

/-- Reassemble the checked depth-eight sibling data without importing the
    coverage wrapper whose soundness proof currently has a Lean defect. -/
def siblingData : List CheckedTree :=
  siblingData1 ++ siblingData2 ++ siblingData3 ++ siblingData4

def localReplaceResidual (t : PackedTable) : List PackedTable :=
  match siblingData.find? (fun e => decide (e.table = t)) with
  | none => [t]
  | some e => e.tree.packedResiduals (BB6.Agent50RootFrontier.unpackTable t)

def refinedRootRoster : List PackedTable :=
  reducedRootRoster.flatMap fun e => localReplaceResidual e.2

/-- The six growth tables are the four one-hole sweeps and two triple sweeps
    already defined in C1Growth. -/
def growthTables : List PackedTable :=
  ([0,1,2,3] : List (Fin 4)).map
    (fun i => packTable (BB6Coverage.Agent50OnesSweep.table i)) ++
  [ packTable (BB6Coverage.Agent50TripleSweep.table false),
    packTable (BB6Coverage.Agent50TripleSweep.table true) ]

def growthCovered (t : PackedTable) : Bool :=
  growthTables.any (fun g => decide (g = t))

def finalRootRoster : List PackedTable :=
  refinedRootRoster.filter (fun t => !growthCovered t)

/-- Reassemble the 98 checked block-pump data entries without importing
    BlockPumpCoverage's theorem layer. -/
def pumpRoster : List CheckedPump :=
  pumpRoster1 ++ pumpRoster2 ++ pumpRoster3 ++ pumpRoster4

def pumpCovered (t : PackedTable) : Bool :=
  pumpRoster.any (fun w => decide (w.table = t))

def dataPumpedRootRoster : List PackedTable :=
  finalRootRoster.filter (fun t => !pumpCovered t)

/-- First exceptional table from the nested-pump catalogue, Boolean false. -/
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

/-- Second exceptional table from the nested-pump catalogue, Boolean true. -/
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

/-- Third exceptional table from the two-block-growth catalogue. -/
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

/-- Data exclusions only; no exceptional-pump nonhalting theorem is used. -/
def exceptionalTables : List PackedTable :=
  [nestedFalse, nestedTrue, doubleGrow]

def exceptionalCovered (t : PackedTable) : Bool :=
  exceptionalTables.any (fun e => decide (e = t))

def canonicalResidualRoster : List PackedTable :=
  dataPumpedRootRoster.filter (fun t => !exceptionalCovered t)

/-- Agent31's frontier, losslessly packed into the common twelve-slot
    representation used by Agent50's recursive certificate. -/
def agent31PackedRoster : List PackedTable :=
  BB6.Agent44SourceRoster.pureRemainingRootRoster.map
    (fun e => BB6.Agent50RootFrontier.packTable e.2)

/-- Exact equality of the two independently generated residual frontiers,
    checked over all twelve transition slots by kernel computation. -/
theorem agent31PackedRoster_perm_canonicalResidualRoster :
    List.Perm agent31PackedRoster canonicalResidualRoster := by
  decide

theorem canonicalResidualRoster_count :
    canonicalResidualRoster.length = 124 := by
  decide

/-- Transfer Agent31's checked 395 weighted bound to the canonical roster.
    The proof uses only Agent31's soundness theorem and the table permutation;
    it does not depend on Agent50's current coverage-wrapper theorems. -/
theorem canonicalResidualRoster_sound_395 :
    ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound 395 m ∨
      ∃ q ∈ canonicalResidualRoster, compatible (BB6.Agent50RootFrontier.unpackTable q) m := by
  intro m hm
  rcases BB6.Agent44SourceRoster.pureRemainingRootRoster_sound m hm with hbound | ⟨e, he, hc⟩
  · exact Or.inl hbound
  · have hpack : BB6.Agent50RootFrontier.packTable e.2 ∈ agent31PackedRoster := by
      exact List.mem_map.mpr ⟨e, he, rfl⟩
    have hcanonical : BB6.Agent50RootFrontier.packTable e.2 ∈ canonicalResidualRoster :=
      (List.Perm.mem_iff agent31PackedRoster_perm_canonicalResidualRoster).mp hpack
    exact Or.inr ⟨BB6.Agent50RootFrontier.packTable e.2, hcanonical, by
      simpa only [BB6.Agent50RootFrontier.unpack_packTable] using hc⟩

#print axioms agent31PackedRoster_perm_canonicalResidualRoster
#print axioms canonicalResidualRoster_count
#print axioms canonicalResidualRoster_sound_395

end BB6.Agent13RosterConvergence
