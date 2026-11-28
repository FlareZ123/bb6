import Raw11Extra132140After150
import Agent5Q0Coarse148
import Q0RosterConsume

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Direct q0-148 successor to Agent44's exact Raw11 299→148 route.

The imported q0-148 parent is the source-kernel-checked complete B=6164
classifier.  This file transports that exact parent by literal same-table
equality and removes precisely one representative from the 148-entry
complement, yielding 147.
-/
namespace BB6.Agent44Raw11Q0148After148
open BB6Coverage BB6.Agent13BlankDelay

def q0148 : PartialMachine := fun (q,b) => match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def prior : List PartialMachine := BB6.Agent44Raw11Extra132140After150.remaining
def closed : List PartialMachine := [q0148]
def remaining : List PartialMachine := Q0RosterConsume.removeCovered prior closed

theorem literal_code :
    BB6.Agent47PhaseFrontier.tableCode q0148 = 27168822759015208 := by
  decide +kernel

theorem member_in_148 : q0148 ∈ prior := by
  have h : prior.any (fun q => Q0ExhaustiveTree.sameTable q q0148) = true := by
    decide +kernel
  obtain ⟨q,hq,he⟩ := List.any_eq_true.mp h
  exact (Q0ExhaustiveTree.sameTable_sound he) ▸ hq

theorem remaining_census :
    (prior.length, remaining.length) = (148,147) := by
  decide +kernel

theorem q0148_cover (B : Nat) (hB : 6164 ≤ B) :
    Cover (WeightedBound B) q0148 := by
  have heq : q0148 = BB6.Agent5Q0Coarse148.parent :=
    BB6.Agent47PhaseFrontier.sameTable_sound (by decide +kernel)
  rw [heq]
  exact Q0RosterConsume.liftCover hB BB6.Agent5Q0Coarse148.cover

theorem raw11_cover_from_147 (B : Nat) (hB : 6164 ≤ B)
    (hRemaining : ∀ p ∈ remaining, ∀ m, compatible p m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent47Raw11Route.parent :=
  BB6.Agent44Raw11Extra132140After150.raw11_cover_from_148 B (by omega)
    (Q0RosterConsume.consume B prior closed
      (by
        intro p hp
        simp only [closed, List.mem_singleton] at hp
        subst p
        exact q0148_cover B hB)
      hRemaining)

#print axioms literal_code
#print axioms member_in_148
#print axioms remaining_census
#print axioms q0148_cover
#print axioms raw11_cover_from_147
end BB6.Agent44Raw11Q0148After148
