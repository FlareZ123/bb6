import Raw139NormalizedE0OneRFFinite

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedE0TenAcceptedFinite

open BB6Coverage
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedE0CutsFinite
open BB6.Agent14Raw139NormalizedE0OneRFFinite

/-- Three further already source-certified original six-hole parent cylinders:
    oneRA Agent48 run 45955243872; oneLB Agent3 run 45969459350;
    oneLD Agent48 run 46026798568. -/
def e0OneRA : PartialMachine := leaf (2, ⟨true, true, 0⟩)
def e0OneLB : PartialMachine := leaf (2, ⟨true, false, 1⟩)
def e0OneLD : PartialMachine := leaf (2, ⟨true, false, 3⟩)

/-- Exact ten physical E0 parent rows, no quotient or complement substitution. -/
def acceptedE0Ten : List PartialMachine :=
  [e0OneRA, e0OneLB, e0OneLD] ++ acceptedSixPlusOneRF

/-- Conditional eleventh row: E0=0LF is awaiting a whole-parent Cover. -/
def acceptedE0Eleven : List PartialMachine :=
  e0ZeroLF :: acceptedE0Ten

theorem more_each_once :
    (remainingTables.filter (fun p => sameTable p e0OneRA)).length = 1 ∧
    (remainingTables.filter (fun p => sameTable p e0OneLB)).length = 1 ∧
    (remainingTables.filter (fun p => sameTable p e0OneLD)).length = 1 := by
  decide

theorem more_disjoint_from_seven :
    matchesAny e0OneRA acceptedSixPlusOneRF = false ∧
    matchesAny e0OneLB acceptedSixPlusOneRF = false ∧
    matchesAny e0OneLD acceptedSixPlusOneRF = false := by
  decide

theorem acceptedTen_each_once :
    ∀ q ∈ acceptedE0Ten,
      (remainingTables.filter (fun p => sameTable p q)).length = 1 := by
  decide

def normalizedAfterTen : List PartialMachine :=
  remainingTables.filter (fun p => !(matchesAny p acceptedE0Ten))

theorem normalizedAfterTen_count : normalizedAfterTen.length = 57 := by
  decide

def normalizedAfterEleven : List PartialMachine :=
  remainingTables.filter (fun p => !(matchesAny p acceptedE0Eleven))

theorem normalizedAfterEleven_count : normalizedAfterEleven.length = 56 := by
  decide

#print axioms more_each_once
#print axioms more_disjoint_from_seven
#print axioms acceptedTen_each_once
#print axioms normalizedAfterTen_count
#print axioms normalizedAfterEleven_count

end BB6.Agent14Raw139NormalizedE0TenAcceptedFinite
