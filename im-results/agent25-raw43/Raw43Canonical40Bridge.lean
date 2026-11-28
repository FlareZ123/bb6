import Raw43ParentComplete
import Raw43Canonical40Membership

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Bridge the source Raw43 parent theorem to the exact literal used by the
accepted Canonical40 roster.  This file is staged until Raw43ParentComplete
has an original-source accepted dependency closure.
-/

namespace BB6.Agent25Raw43Canonical40Bridge

open BB6Coverage BB6.Agent31FourHoleRoster

abbrev p : PartialMachine := BB6.Agent25Raw43Canonical40Membership.p

theorem literal_eq_source :
    p = BB6.Agent25Raw43Parent.parent :=
  sameTable_sound (by decide)

theorem parent_unique_in_roster40 :
    (BB6.Agent31Canonical40Extra57.roster40.filter
      (fun e => sameTable e.2 p)).length = 1 :=
  BB6.Agent25Raw43Canonical40Membership.parent_present

theorem weighted_cover (B : Nat) (hB : 11292 ≤ B) :
    Cover (WeightedBound B) p := by
  rw [literal_eq_source]
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent38Raw43ParentComplete.all_completions m hm k d hk hd) hB

theorem cover_at_canonical40_floor :
    Cover (WeightedBound 6766859) p :=
  weighted_cover 6766859 (by decide)

#print axioms literal_eq_source
#print axioms parent_unique_in_roster40
#print axioms weighted_cover
#print axioms cover_at_canonical40_floor

end BB6.Agent25Raw43Canonical40Bridge
