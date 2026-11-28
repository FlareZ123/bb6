import Raw39CompleteJoin
import Raw39Canonical40Membership

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Proposed final Raw39 accepted-roster bridge, deliberately separated from the
source-accepted Canonical40 predecessor. Requires successful source/object
integration of all eleven Raw39 child certificates; it has NOT been compiled
in that combined closure yet. Source must not be represented as accepted until
Lean kernel and transitive axiom audit succeed.
-/

namespace BB6.Agent11Raw39Canonical40Bridge

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent11SemanticChunks
open BB6.Agent31FourHoleRoster

abbrev p : PartialMachine := BB6.Agent11Raw39Canonical40Membership.p

theorem literal_eq_source : p = BB6.Agent11Raw39AcceptedSix.p39 :=
  sameTable_sound (by decide)

theorem parent_unique_in_roster40 :
    (BB6.Agent31Canonical40Extra57.roster40.filter
      (fun e => sameTable e.2 p)).length = 1 :=
  BB6.Agent11Raw39Canonical40Membership.parent_present

theorem weighted_cover (B : Nat) (hB : 28311 ≤ B) :
    Cover (WeightedBound B) p := by
  rw [literal_eq_source]
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent11Raw39Closed.parent_bound m hm k d hk hd) hB

theorem cover_at_champion_threshold :
    Cover (WeightedBound 6766859) p :=
  weighted_cover 6766859 (by decide)

#print axioms literal_eq_source
#print axioms parent_unique_in_roster40
#print axioms weighted_cover
#print axioms cover_at_champion_threshold

end BB6.Agent11Raw39Canonical40Bridge
