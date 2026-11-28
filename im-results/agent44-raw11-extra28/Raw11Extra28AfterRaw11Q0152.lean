import Raw11Q0CombinedExtra
import Raw11Extra28AllChildren
import Q0RosterConsume

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
An exact-complement conditional Raw11 consumer for Extra28, starting from
the locally Lean-checked 152-entry Raw11Q0CombinedExtra route. This source
does not assume the Extra28 Cover; it receives it as an explicit premise.
It removes only one *literal* table via the already-sound sameTable filter,
not all of its overlapping physical completions or any unproved siblings.
-/
namespace BB6.Agent44Extra28Raw11Next
open BB6Coverage BB6.Agent13BlankDelay

def extra28 : PartialMachine := BB6.Agent44Extra28AllChildren.parent
def closed : List PartialMachine := [extra28]
def prior : List PartialMachine := BB6.Agent47Raw11Q0CombinedExtra.remaining
def remaining : List PartialMachine := Q0RosterConsume.removeCovered prior closed

theorem literal_code :
    BB6.Agent47PhaseFrontier.tableCode extra28 = 26318896606190888 := by
  decide +kernel

theorem member_in_152 : extra28 ∈ prior := by decide +kernel

theorem no_other_removed :
    (prior.length, remaining.length) = (152,151) := by decide +kernel

theorem parent_from_151 (B : Nat) (hB : 4663 ≤ B)
    (hExtra : Cover (WeightedBound 158) extra28)
    (hRemaining : ∀ p ∈ remaining, ∀ m, compatible p m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent47Raw11Route.parent :=
  BB6.Agent47Raw11Q0CombinedExtra.cover_from_remaining B hB
    (Q0RosterConsume.consume B prior closed
      (by
        intro p hp
        simp only [closed, List.mem_singleton] at hp
        subst p
        exact Q0RosterConsume.liftCover
          (Nat.le_trans (by decide : 158 ≤ 4663) hB) hExtra)
      hRemaining)

#print axioms literal_code
#print axioms member_in_152
#print axioms no_other_removed
#print axioms parent_from_151
end BB6.Agent44Extra28Raw11Next
