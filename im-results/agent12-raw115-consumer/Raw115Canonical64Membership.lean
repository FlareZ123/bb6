import Canonical64Raw120Integrated
import Raw115Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent12Raw115Canonical64Membership

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier
open BB6.Agent3Canonical64Raw120

/-- Canonical-124 residual 115, with E1=0RD. -/
abbrev p115 : PartialMachine := BB6.Agent47Raw115.parent

theorem p115_root :
    p115 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent47Raw115.parent_root

/-- The exact parent bound can be lifted to the common score floor. -/
theorem cover115 (B : Nat) (hB : 7014 ≤ B) :
    Cover (WeightedBound B) p115 :=
  Cover.leaf _ (fun m hm k d hk hd =>
    Nat.le_trans (BB6.Agent47Raw115.all_completions m hm k d hk hd) hB)

/-- Membership in the accepted common base, with no competing roster. -/
theorem p115_parent_count64 :
    (roster64.filter (fun e => sameTable e.2 p115)).length = 1 := by
  decide

#print axioms p115_root
#print axioms cover115
#print axioms p115_parent_count64

end BB6.Agent12Raw115Canonical64Membership
