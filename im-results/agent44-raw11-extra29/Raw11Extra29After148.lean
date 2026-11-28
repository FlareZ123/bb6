import Raw11Extra132140After150
import Agent5Raw11Extra29
import Q0RosterConsume

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Exact successor to the accepted Raw11 299→148 conditional interface.

This consumes the literal Raw11 extra-roster index 29 parent
`1RB0LB_1RC1LC_0LA0RD_------_------_------`.  The only deletion from the
148-entry predecessor is justified by exact same-table membership and the
source-checked complete parent Cover.  This is a conditional 148→147
reduction, not a BB(6) maximality theorem.
-/
namespace BB6.Agent44Raw11Extra29After148
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent47PhaseFrontier (tableCode)

def parent : PartialMachine := fun (q,b) => match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,3⟩)
  | _,_ => none

def prior : List PartialMachine := BB6.Agent44Raw11Extra132140After150.remaining
def closed : List PartialMachine := [parent]
def remaining : List PartialMachine := Q0RosterConsume.removeCovered prior closed

theorem literal_code : tableCode parent = 26318896915106664 := by
  decide +kernel

theorem parent_matches_source : parent = BB6.Agent5Raw11Extra29.parent :=
  BB6.Agent47PhaseFrontier.sameTable_sound (by decide +kernel)

theorem member_in_148 : parent ∈ prior := by
  have h : prior.any (fun q => Q0ExhaustiveTree.sameTable q parent) = true := by
    decide +kernel
  obtain ⟨q,hq,he⟩ := List.any_eq_true.mp h
  exact (Q0ExhaustiveTree.sameTable_sound he) ▸ hq

theorem remaining_census :
    (prior.length, remaining.length) = (148,147) := by
  decide +kernel

theorem parent_cover (B : Nat) (hB : 4663 ≤ B) :
    Cover (WeightedBound B) parent := by
  rw [parent_matches_source]
  exact Q0RosterConsume.liftCover (by omega) BB6.Agent5Raw11Extra29.cover

theorem raw11_cover_from_147 (B : Nat) (hB : 4663 ≤ B)
    (hRemaining : ∀ p ∈ remaining, ∀ m, compatible p m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent47Raw11Route.parent :=
  BB6.Agent44Raw11Extra132140After150.raw11_cover_from_148 B hB
    (Q0RosterConsume.consume B prior closed
      (by
        intro p hp
        simp only [closed, List.mem_singleton] at hp
        subst p
        exact parent_cover B hB)
      hRemaining)

#print axioms parent_matches_source
#print axioms member_in_148
#print axioms remaining_census
#print axioms parent_cover
#print axioms raw11_cover_from_147
end BB6.Agent44Raw11Extra29After148
