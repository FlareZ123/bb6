import CanonicalSelectedParentIntegrated
import Raw113ParentExact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical59Raw113Membership

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch

/-- Raw113's exact E1 = 1RC parent, independently named for the 59-roster delta. -/
abbrev e1Base : PartialMachine := (pathEnd root 2 (path.take 4)).1
abbrev p113 : PartialMachine :=
  refine e1Base (4,true) (some ⟨true,true,2⟩)
abbrev p113Source : PartialMachine := BB6.Agent25Raw113.p113

theorem p113_source_eq : p113 = p113Source := by
  exact sameTable_sound (by decide)

theorem p113_count64 :
    (BB6.Agent3Canonical64Raw120.roster64.filter
      (fun e => sameTable e.2 p113)).length = 1 := by decide

theorem p113_count59 :
    (BB6.Agent32CanonicalSelectedIntegrated.rosterSelected.filter
      (fun e => sameTable e.2 p113)).length = 1 := by decide

theorem p113_root :
    p113 initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem p113_cover : Cover (WeightedBound 6766859) p113 := by
  rw [p113_source_eq]
  exact BB6.Agent25Raw113.cover113 6766859 (by decide)

#print axioms p113_source_eq
#print axioms p113_count64
#print axioms p113_count59
#print axioms p113_root
#print axioms p113_cover

end BB6.Agent31Canonical59Raw113Membership
