import Raw11Extra28After151
import Agent5Raw11Extra132
import Agent5Raw11Extra140
import Q0RosterConsume

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Exact two-parent successor to the source-accepted Raw11 299→150 route.

Extra28 has already been consumed in the imported predecessor. This module
removes exactly Extra132 and Extra140 from that 150-entry complement, using
their independently source-kernel-checked Covers and literal same-table
transport. The resulting complement has exactly 148 entries.
-/
namespace BB6.Agent44Raw11Extra132140After150
open BB6Coverage BB6.Agent13BlankDelay

def pExtra132 : PartialMachine := fun (q,b) => match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,2⟩)
  | _,_ => none

def pExtra140 : PartialMachine := fun (q,b) => match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | _,_ => none

def parents : List PartialMachine := [pExtra132,pExtra140]
def prior : List PartialMachine := BB6.Agent47Raw11Extra28After151.remaining
def remaining : List PartialMachine := Q0RosterConsume.removeCovered prior parents

theorem literal_codes :
    parents.map BB6.Agent47PhaseFrontier.tableCode =
      [27874661676483464,27872991061794760] := by
  decide +kernel

theorem member_via_sameTable (p : PartialMachine)
    (h : prior.any (fun q => Q0ExhaustiveTree.sameTable q p) = true) :
    p ∈ prior := by
  obtain ⟨q,hq,he⟩ := List.any_eq_true.mp h
  exact (Q0ExhaustiveTree.sameTable_sound he) ▸ hq

theorem all_members_in_150 : ∀ p ∈ parents, p ∈ prior := by
  intro p hp
  simp [parents] at hp
  rcases hp with rfl | rfl <;>
    exact member_via_sameTable _ (by decide +kernel)

theorem exact_census :
    (prior.length,remaining.length) = (150,148) := by
  decide +kernel

theorem extra132_cover (B : Nat) (hB : 4663 ≤ B) :
    Cover (WeightedBound B) pExtra132 := by
  have heq : pExtra132 = BB6.Agent5Raw11Extra132.parent :=
    BB6.Agent47PhaseFrontier.sameTable_sound (by decide +kernel)
  rw [heq]
  exact Q0RosterConsume.liftCover (by omega) BB6.Agent5Raw11Extra132.cover

theorem extra140_cover (B : Nat) (hB : 4663 ≤ B) :
    Cover (WeightedBound B) pExtra140 := by
  have heq : pExtra140 = BB6.Agent5Raw11Extra140.parent :=
    BB6.Agent47PhaseFrontier.sameTable_sound (by decide +kernel)
  rw [heq]
  exact Q0RosterConsume.liftCover (by omega) BB6.Agent5Raw11Extra140.cover

theorem all_parent_covers (B : Nat) (hB : 4663 ≤ B) :
    ∀ p ∈ parents, Cover (WeightedBound B) p := by
  intro p hp
  simp [parents] at hp
  rcases hp with rfl | rfl
  · exact extra132_cover B hB
  · exact extra140_cover B hB

theorem raw11_cover_from_148 (B : Nat) (hB : 4663 ≤ B)
    (hRemaining : ∀ p ∈ remaining, ∀ m, compatible p m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent47Raw11Route.parent :=
  BB6.Agent47Raw11Extra28After151.raw11_cover_from_150 B hB
    (Q0RosterConsume.consume B prior parents (all_parent_covers B hB) hRemaining)

#print axioms literal_codes
#print axioms all_members_in_150
#print axioms exact_census
#print axioms extra132_cover
#print axioms extra140_cover
#print axioms raw11_cover_from_148
end BB6.Agent44Raw11Extra132140After150
