import Raw11Extra28After151
import Q0RosterConsume

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Exact crosswalk from the accepted Raw11 150-entry complement to the two
pending Extra parents and the three source-normalized q0 parents 148/150/151.

This module intentionally takes those five parent Covers as hypotheses.
Its purpose is to prove literal membership, distinctness through exact
sameTable removal, and the resulting 150→145 complement without conflating
candidate/local source work with accepted parent Covers.
-/
namespace BB6.Agent47Raw11FiveLiveAfter150
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

def q0148 : PartialMachine := fun (q,b) => match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def q0150 : PartialMachine := fun (q,b) => match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,false,3⟩)
  | _,_ => none

def q0151 : PartialMachine := fun (q,b) => match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,true,3⟩)
  | _,_ => none

def parents : List PartialMachine := [pExtra132,pExtra140,q0148,q0150,q0151]
def prior : List PartialMachine := BB6.Agent47Raw11Extra28After151.remaining
def remaining : List PartialMachine := Q0RosterConsume.removeCovered prior parents

theorem literal_codes :
    parents.map BB6.Agent47PhaseFrontier.tableCode =
      [27874661676483464, 27872991061794760,
       27168822759015208, 27168823376846760, 27168823685762536] := by
  decide +kernel

theorem member_via_sameTable (p : PartialMachine)
    (h : prior.any (fun q => Q0ExhaustiveTree.sameTable q p) = true) :
    p ∈ prior := by
  obtain ⟨q,hq,he⟩ := List.any_eq_true.mp h
  exact (Q0ExhaustiveTree.sameTable_sound he) ▸ hq

theorem all_members_in_150 : ∀ p ∈ parents, p ∈ prior := by
  intro p hp
  simp [parents] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
    exact member_via_sameTable _ (by decide +kernel)

theorem exact_census :
    (prior.length, remaining.length) = (150,145) := by
  decide +kernel

theorem raw11_cover_from_145 (B : Nat) (hB : 4663 ≤ B)
    (hExtra132 : Cover (WeightedBound B) pExtra132)
    (hExtra140 : Cover (WeightedBound B) pExtra140)
    (hQ0148 : Cover (WeightedBound B) q0148)
    (hQ0150 : Cover (WeightedBound B) q0150)
    (hQ0151 : Cover (WeightedBound B) q0151)
    (hRemaining : ∀ p ∈ remaining, ∀ m, compatible p m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent47Raw11Route.parent :=
  BB6.Agent47Raw11Extra28After151.raw11_cover_from_150 B hB
    (Q0RosterConsume.consume B prior parents
      (by
        intro p hp
        simp [parents] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl
        · exact hExtra132
        · exact hExtra140
        · exact hQ0148
        · exact hQ0150
        · exact hQ0151)
      hRemaining)

#print axioms literal_codes
#print axioms all_members_in_150
#print axioms exact_census
#print axioms raw11_cover_from_145
end BB6.Agent47Raw11FiveLiveAfter150
