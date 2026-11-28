import Raw11Route
import Raw11Extra28AllChildren
import Q0RosterConsume

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Source-checked conditional Raw11 first-stage consumption:
one exact Extra28 cylinder can be eliminated from the 294-entry
Raw11Route.remaining list, at any B≥234, whenever a genuine
Cover (WeightedBound 158) Extra28 has been established.

The transition equality is checked by the existing sameTable predicate,
not by code arithmetic. Every other residual remains in the obligation.
This theorem does not import an unverified proof of Extra28.
-/
namespace BB6.Agent44Extra28Raw11Root
open BB6Coverage BB6.Agent13BlankDelay

def extra28 : PartialMachine := BB6.Agent44Extra28AllChildren.parent
def prior : List PartialMachine := BB6.Agent47Raw11Route.remaining
def closed : List PartialMachine := [extra28]
def remaining : List PartialMachine := Q0RosterConsume.removeCovered prior closed

theorem exact_code :
    BB6.Agent47PhaseFrontier.tableCode extra28 = 26318896606190888 := by
  decide +kernel

theorem exact_member : extra28 ∈ prior := by decide +kernel

theorem exact_complement :
    (prior.length, remaining.length) = (294,293) := by decide +kernel

theorem cover_from_293 (B : Nat) (hB : 234 ≤ B)
    (hExtra : Cover (WeightedBound 158) extra28)
    (hRemaining : ∀ p ∈ remaining, ∀ m, compatible p m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent47Raw11Route.parent :=
  BB6.Agent47Raw11Route.cover_from_remaining B hB
    (Q0RosterConsume.consume B prior closed
      (by
        intro p hp
        simp only [closed, List.mem_singleton] at hp
        subst p
        exact Q0RosterConsume.liftCover
          (Nat.le_trans (by decide : 158 ≤ 234) hB) hExtra)
      hRemaining)

#print axioms exact_code
#print axioms exact_member
#print axioms exact_complement
#print axioms cover_from_293
end BB6.Agent44Extra28Raw11Root
