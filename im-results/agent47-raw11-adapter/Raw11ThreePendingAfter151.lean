import Raw11Q0Root53After152
import Raw11Extra28LiteralComplete
import Agent5Raw11Extra132
import Agent5Raw11Extra140
import Q0RosterConsume

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Exact three-parent successor to the source-accepted Raw11 299→151 route.

This consumes precisely Extra28, Extra132 and Extra140 after q0-root53 has
already been removed. Each imported parent theorem is independently
source-kernel checked; literal table equality is re-established here before
using it. The resulting complement has exactly 148 entries.
-/
namespace BB6.Agent47Raw11ThreePendingAfter151
open BB6Coverage BB6.Agent13BlankDelay

def pExtra28 : PartialMachine := BB6.Agent44Extra28AllChildren.parent

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

def parents : List PartialMachine := [pExtra28,pExtra132,pExtra140]
def prior : List PartialMachine := BB6.Agent47Q0Root53After152.remaining
def remaining : List PartialMachine := Q0RosterConsume.removeCovered prior parents

theorem literal_codes :
    parents.map BB6.Agent47PhaseFrontier.tableCode =
      [26318896606190888, 27874661676483464, 27872991061794760] := by
  decide +kernel

theorem member_via_sameTable (p : PartialMachine)
    (h : prior.any (fun q => Q0ExhaustiveTree.sameTable q p) = true) :
    p ∈ prior := by
  obtain ⟨q,hq,he⟩ := List.any_eq_true.mp h
  exact (Q0ExhaustiveTree.sameTable_sound he) ▸ hq

theorem all_members_in_151 : ∀ p ∈ parents, p ∈ prior := by
  intro p hp
  simp [parents] at hp
  rcases hp with rfl | rfl | rfl <;>
    exact member_via_sameTable _ (by decide +kernel)

theorem exact_census :
    (prior.length,remaining.length) = (151,148) := by
  decide +kernel

theorem extra28_cover (B : Nat) (hB : 4663 ≤ B) :
    Cover (WeightedBound B) pExtra28 :=
  Q0RosterConsume.liftCover
    (Nat.le_trans (by decide : 158 ≤ 4663) hB)
    BB6.Agent44Extra28Completed.literal_complete

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
  rcases hp with rfl | rfl | rfl
  · exact extra28_cover B hB
  · exact extra132_cover B hB
  · exact extra140_cover B hB

theorem raw11_cover_from_148 (B : Nat) (hB : 4663 ≤ B)
    (hRemaining : ∀ p ∈ remaining, ∀ m, compatible p m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent47Raw11Route.parent :=
  BB6.Agent47Q0Root53After152.raw11_cover_from_151 B hB
    (Q0RosterConsume.consume B prior parents (all_parent_covers B hB) hRemaining)

#print axioms literal_codes
#print axioms all_members_in_151
#print axioms exact_census
#print axioms extra28_cover
#print axioms extra132_cover
#print axioms extra140_cover
#print axioms raw11_cover_from_148
end BB6.Agent47Raw11ThreePendingAfter151
