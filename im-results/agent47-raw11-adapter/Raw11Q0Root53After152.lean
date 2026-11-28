import Raw11Q0CombinedExtra
import Q0Root53Parent
import Q0RosterConsume

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Exact-complement source bridge for the full q0 root53 parent. The source tree
is separately checked by Q0Root53.safe_root; its 30,793-node exhaustive proof
is not assumed merely from the search manifest. This module never deletes a
sibling except by literal table equality in removeCovered.
-/
namespace BB6.Agent47Q0Root53After152
open BB6Coverage BB6.Agent13BlankDelay

def parent : PartialMachine := Q0Root53.rootParent
def prior : List PartialMachine := BB6.Agent47Raw11Q0CombinedExtra.remaining
def closed : List PartialMachine := [parent]
def remaining : List PartialMachine := Q0RosterConsume.removeCovered prior closed

theorem literal_code :
    BB6.Agent47PhaseFrontier.tableCode parent = 27873617542988488 := by
  decide +kernel

theorem member_in_152 : parent ∈ prior := by decide +kernel

theorem exact_complement :
    remaining = prior.filter (fun q => !BB6.Agent47PhaseFrontier.sameTable q parent) := by
  rfl

theorem remaining_census :
    (prior.length, remaining.length) = (152,151) := by decide +kernel

theorem parent_cover : Cover (WeightedBound 208) parent :=
  Q0Root53.safe_root

theorem raw11_cover_from_151 (B : Nat) (hB : 4663 ≤ B)
    (hRemaining : ∀ p ∈ remaining, ∀ m, compatible p m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent47Raw11Route.parent :=
  BB6.Agent47Raw11Q0CombinedExtra.cover_from_remaining B hB
    (Q0RosterConsume.consume B prior closed
      (by
        intro p hp
        simp only [closed, List.mem_singleton] at hp
        subst p
        exact Q0RosterConsume.liftCover
          (Nat.le_trans (by decide : 208 ≤ 4663) hB) parent_cover)
      hRemaining)

#print axioms literal_code
#print axioms member_in_152
#print axioms remaining_census
#print axioms parent_cover
#print axioms raw11_cover_from_151
end BB6.Agent47Q0Root53After152
