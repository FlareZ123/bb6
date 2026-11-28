import Raw11Extra140After150
import Agent5Raw11Extra132
import Q0RosterConsume

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Exact one-parent successor to the source-accepted Raw11 299→149 route.

Extra140 has already been discharged. This module removes exactly Extra132
from that 149-entry complement after importing its independently source-checked
parent Cover. No sibling is deleted except by literal sameTable equality.
-/
namespace BB6.Agent44Raw11Extra132After149
open BB6Coverage BB6.Agent13BlankDelay

def parent : PartialMachine := fun (q,b) => match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,2⟩)
  | _,_ => none

def prior : List PartialMachine := BB6.Agent44Raw11Extra140After150.remaining
def closed : List PartialMachine := [parent]
def remaining : List PartialMachine := Q0RosterConsume.removeCovered prior closed

theorem literal_code :
    BB6.Agent47PhaseFrontier.tableCode parent = 27874661676483464 := by
  decide +kernel

theorem member_in_149 : parent ∈ prior := by
  have h : prior.any (fun q => Q0ExhaustiveTree.sameTable q parent) = true := by
    decide +kernel
  obtain ⟨q,hq,he⟩ := List.any_eq_true.mp h
  exact (Q0ExhaustiveTree.sameTable_sound he) ▸ hq

theorem remaining_census :
    (prior.length, remaining.length) = (149,148) := by
  decide +kernel

theorem parent_cover (B : Nat) (hB : 4663 ≤ B) :
    Cover (WeightedBound B) parent := by
  have heq : parent = BB6.Agent5Raw11Extra132.parent :=
    BB6.Agent47PhaseFrontier.sameTable_sound (by decide +kernel)
  rw [heq]
  exact Q0RosterConsume.liftCover
    (Nat.le_trans (by decide : 691 ≤ 4663) hB) BB6.Agent5Raw11Extra132.cover

theorem raw11_cover_from_148 (B : Nat) (hB : 4663 ≤ B)
    (hRemaining : ∀ p ∈ remaining, ∀ m, compatible p m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent47Raw11Route.parent :=
  BB6.Agent44Raw11Extra140After150.raw11_cover_from_149 B hB
    (Q0RosterConsume.consume B prior closed
      (by
        intro p hp
        simp only [closed, List.mem_singleton] at hp
        subst p
        exact parent_cover B hB)
      hRemaining)

#print axioms literal_code
#print axioms member_in_149
#print axioms remaining_census
#print axioms parent_cover
#print axioms raw11_cover_from_148
end BB6.Agent44Raw11Extra132After149
