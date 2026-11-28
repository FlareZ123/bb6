import Raw11Q0Root53After152
import Raw11Extra28LiteralComplete
import Q0RosterConsume

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Exact successor to the source-accepted Raw11 299→151 route.

The q0-root53 parent has already been discharged in
BB6.Agent47Q0Root53After152. This module removes exactly the distinct
Extra28 literal from that 151-entry complement and imports the separately
source-assembled complete Extra28 parent Cover. No sibling is deleted
except by literal sameTable equality.
-/
namespace BB6.Agent47Raw11Extra28After151
open BB6Coverage BB6.Agent13BlankDelay

def parent : PartialMachine := BB6.Agent44Extra28AllChildren.parent
def prior : List PartialMachine := BB6.Agent47Q0Root53After152.remaining
def closed : List PartialMachine := [parent]
def remaining : List PartialMachine := Q0RosterConsume.removeCovered prior closed

theorem literal_code :
    BB6.Agent47PhaseFrontier.tableCode parent = 26318896606190888 := by
  decide +kernel

theorem member_in_151 : parent ∈ prior := by
  have h : prior.any (fun q => Q0ExhaustiveTree.sameTable q parent) = true := by
    decide +kernel
  obtain ⟨q,hq,he⟩ := List.any_eq_true.mp h
  exact (Q0ExhaustiveTree.sameTable_sound he) ▸ hq

theorem remaining_census :
    (prior.length, remaining.length) = (151,150) := by
  decide +kernel

theorem parent_cover : Cover (WeightedBound 158) parent :=
  BB6.Agent44Extra28Completed.literal_complete

theorem raw11_cover_from_150 (B : Nat) (hB : 4663 ≤ B)
    (hRemaining : ∀ p ∈ remaining, ∀ m, compatible p m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent47Raw11Route.parent :=
  BB6.Agent47Q0Root53After152.raw11_cover_from_151 B hB
    (Q0RosterConsume.consume B prior closed
      (by
        intro p hp
        simp only [closed, List.mem_singleton] at hp
        subst p
        exact Q0RosterConsume.liftCover
          (Nat.le_trans (by decide : 158 ≤ 4663) hB) parent_cover)
      hRemaining)

#print axioms literal_code
#print axioms member_in_151
#print axioms remaining_census
#print axioms parent_cover
#print axioms raw11_cover_from_150
end BB6.Agent47Raw11Extra28After151
