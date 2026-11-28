import Raw11Extra28After151
import Agent5Raw11Extra140
import Q0RosterConsume

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Exact one-parent successor to the source-accepted Raw11 299→150 route.

The q0-root53 and Extra28 parents have already been discharged. This module
removes exactly Extra140 from that 150-entry complement, after importing its
independently source-kernel-checked parent Cover. No sibling is deleted except
by literal sameTable equality.
-/
namespace BB6.Agent44Raw11Extra140After150
open BB6Coverage BB6.Agent13BlankDelay

def parent : PartialMachine := fun (q,b) => match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | _,_ => none

def prior : List PartialMachine := BB6.Agent47Raw11Extra28After151.remaining
def closed : List PartialMachine := [parent]
def remaining : List PartialMachine := Q0RosterConsume.removeCovered prior closed

theorem literal_code :
    BB6.Agent47PhaseFrontier.tableCode parent = 27872991061794760 := by
  decide +kernel

theorem member_in_150 : parent ∈ prior := by
  have h : prior.any (fun q => Q0ExhaustiveTree.sameTable q parent) = true := by
    decide +kernel
  obtain ⟨q,hq,he⟩ := List.any_eq_true.mp h
  exact (Q0ExhaustiveTree.sameTable_sound he) ▸ hq

theorem remaining_census :
    (prior.length, remaining.length) = (150,149) := by
  decide +kernel

theorem parent_cover (B : Nat) (hB : 4663 ≤ B) :
    Cover (WeightedBound B) parent := by
  have heq : parent = BB6.Agent5Raw11Extra140.parent :=
    BB6.Agent47PhaseFrontier.sameTable_sound (by decide +kernel)
  rw [heq]
  exact Q0RosterConsume.liftCover (by omega) BB6.Agent5Raw11Extra140.cover

theorem raw11_cover_from_149 (B : Nat) (hB : 4663 ≤ B)
    (hRemaining : ∀ p ∈ remaining, ∀ m, compatible p m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent47Raw11Route.parent :=
  BB6.Agent47Raw11Extra28After151.raw11_cover_from_150 B hB
    (Q0RosterConsume.consume B prior closed
      (by
        intro p hp
        simp only [closed, List.mem_singleton] at hp
        subst p
        exact parent_cover B hB)
      hRemaining)

#print axioms literal_code
#print axioms member_in_150
#print axioms remaining_census
#print axioms parent_cover
#print axioms raw11_cover_from_149
end BB6.Agent44Raw11Extra140After150
