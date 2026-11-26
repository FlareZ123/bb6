import CanonicalSelectedParentIntegrated
import Raw112ClosedCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent17Canonical59Raw112Membership

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6.Agent31Canonical59Membership

/-- Raw112 is the E1 = 1LC first-one parent. -/
abbrev e1Base : PartialMachine := (pathEnd root 2 (path.take 4)).1
abbrev p112 : PartialMachine :=
  refine e1Base (4,true) (some ⟨true,false,2⟩)

/-- Exact source parent from the Raw112 producer. -/
abbrev p112Source : PartialMachine := BB6.Agent47Raw112.parent

theorem p112_source_eq : p112 = p112Source := by
  exact sameTable_sound (by decide)

theorem p112_count64 :
    (BB6.Agent3Canonical64Raw120.roster64.filter
      (fun e => sameTable e.2 p112)).length = 1 := by decide

theorem p112_count59 :
    (BB6.Agent32CanonicalSelectedIntegrated.rosterSelected.filter
      (fun e => sameTable e.2 p112)).length = 1 := by decide

theorem p112_root :
    p112 initialSlot = some (some ⟨true,true,1⟩) := by decide

/-- Lift the source-accepted Raw112 parent Cover at 100,000 to the common
    Canonical59 score floor, without changing the machine or its table. -/
theorem p112_cover : Cover (WeightedBound 6766859) p112 := by
  rw [p112_source_eq]
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent47Raw112.parent_cover.sound m hm k d hk hd)
    (by decide)

#print axioms p112_source_eq
#print axioms p112_count64
#print axioms p112_count59
#print axioms p112_root
#print axioms p112_cover

end BB6.Agent17Canonical59Raw112Membership
