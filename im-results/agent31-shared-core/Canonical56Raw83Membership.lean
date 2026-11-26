import Canonical56Raw59Graft
import Canonical58Raw83Membership

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical56Raw83Membership

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent31StableParentBatch
open BB6.Agent31Canonical59Membership
open BB6.Agent31Canonical59Raw113Membership
open BB6.Agent17Canonical59Raw112Membership
open BB6.Agent32Canonical56Raw59Graft
open BB6.Agent31Canonical58Raw83Membership
open BB6.Agent10Raw83
open BB6ChampionArithmetic

/-- Reuse the exact four-hole Raw83 table already checked against its source. -/
abbrev p83 : PartialMachine := BB6.Agent31Canonical58Raw83Membership.p83

/-- Raw83 remains a unique member after the Raw113, Raw112 and Raw59 cuts. -/
theorem p83_count56 :
    (BB6.Agent32Canonical56Raw59Graft.roster56.filter
      (fun e => sameTable e.2 p83)).length = 1 := by
  decide

/-- The Raw83 parent is distinct from all three previously consumed parents. -/
theorem p83_distinct_from_previous :
    ∀ p ∈ [BB6.Agent31Canonical59Membership.p59,
            BB6.Agent17Canonical59Raw112Membership.p112,
            BB6.Agent31Canonical59Raw113Membership.p113],
      sameTable p p83 = false := by
  decide

/-- The exact table remains the original Raw83 parent. -/
theorem p83_source_eq : p83 = BB6.Agent10Raw83.parent := by
  exact sameTable_sound (by decide)

/-- The original first-one root transition is retained. -/
theorem p83_root :
    p83 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent31Canonical58Raw83Membership.p83_root

/-- Lift the source-accepted 514 bound to the common champion-score floor. -/
theorem p83_cover : Cover (WeightedBound 6766859) p83 := by
  rw [p83_source_eq]
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent10Raw83.all_completions m hm k d hk hd) (by decide)

#print axioms p83_count56
#print axioms p83_distinct_from_previous
#print axioms p83_source_eq
#print axioms p83_root
#print axioms p83_cover

end BB6.Agent31Canonical56Raw83Membership
