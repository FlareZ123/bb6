import Raw139Normalized
import ChampionResidualSourceSiblingIntegrationExtended

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent3Raw139E0Canonical68Probe

open BB6Coverage
open BB6.Agent6Raw139Normalized
open BB6.Agent6ChampionRaw139SiblingExtended

/-- The historical E0=0RA leaf table, tested against the active Canonical68
    raw139 descendant frontier. -/
def e0Row : Fin 7 × Move := (2, ⟨false, true, 0⟩)

def e0Table : PartialMachine := leaf e0Row

theorem e0_table_present_in_80 :
    ∃ e ∈ remainingRaw139AfterFortyThree,
      sameTable e.2 e0Table = true := by decide

theorem e0_table_present_in_81 :
    ∃ e ∈ remainingRaw139AfterFortyTwo,
      sameTable e.2 e0Table = true := by decide

theorem e0_table_present_in_93 :
    ∃ e ∈ remainingRaw139AfterThirty,
      sameTable e.2 e0Table = true := by decide

theorem e0_table_occurs_once_in_80 :
    (remainingRaw139AfterFortyThree.filter
      (fun e => sameTable e.2 e0Table)).length = 1 := by decide

#print axioms e0_table_present_in_80
#print axioms e0_table_present_in_81
#print axioms e0_table_present_in_93
#print axioms e0_table_occurs_once_in_80

end BB6.Agent3Raw139E0Canonical68Probe
