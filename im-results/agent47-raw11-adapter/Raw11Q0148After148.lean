import Raw11ThreePendingAfter151
import Q0RosterConsume

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Exact conditional successor for the frozen q0-148 parent after the three
Extra parents are consumed. The q0-148 Cover is deliberately an explicit
same-B hypothesis here because its full source assembly has a local threshold
above 4663; the eventual accepted parent theorem can be lifted to whatever
global B is used without changing this exact complement proof.
-/
namespace BB6.Agent47Raw11Q0148After148
open BB6Coverage BB6.Agent13BlankDelay

def q0148 : PartialMachine := fun (q,b) => match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def prior : List PartialMachine := BB6.Agent47Raw11ThreePendingAfter151.remaining
def closed : List PartialMachine := [q0148]
def remaining : List PartialMachine := Q0RosterConsume.removeCovered prior closed

theorem literal_code :
    BB6.Agent47PhaseFrontier.tableCode q0148 = 27872153278554440 := by
  decide +kernel

theorem member_in_148 : q0148 ∈ prior := by
  have h : prior.any (fun q => Q0ExhaustiveTree.sameTable q q0148) = true := by
    decide +kernel
  obtain ⟨q,hq,he⟩ := List.any_eq_true.mp h
  exact (Q0ExhaustiveTree.sameTable_sound he) ▸ hq

theorem exact_census :
    (prior.length, remaining.length) = (148,147) := by
  decide +kernel

theorem raw11_cover_from_147 (B : Nat) (hB : 4663 ≤ B)
    (hQ0148 : Cover (WeightedBound B) q0148)
    (hRemaining : ∀ p ∈ remaining, ∀ m, compatible p m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent47Raw11Route.parent :=
  BB6.Agent47Raw11ThreePendingAfter151.raw11_cover_from_148 B hB
    (Q0RosterConsume.consume B prior closed
      (by
        intro p hp
        simp only [closed, List.mem_singleton] at hp
        subst p
        exact hQ0148)
      hRemaining)

#print axioms literal_code
#print axioms member_in_148
#print axioms exact_census
#print axioms raw11_cover_from_147
end BB6.Agent47Raw11Q0148After148
