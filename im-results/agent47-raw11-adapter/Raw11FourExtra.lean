import Raw11Q0Held156
import Agent5Raw11Extra84
import Agent5Raw11Extra131
import Agent5Raw11Extra133
import Agent5Raw11Extra134

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw11FourExtra
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent47PhaseFrontier (tableCode)

def parents : List PartialMachine := [BB6.Agent5Raw11Extra84.parent,
  BB6.Agent5Raw11Extra131.parent, BB6.Agent5Raw11Extra133.parent,
  BB6.Agent5Raw11Extra134.parent]

theorem covers (B : Nat) (hB : 4663 ≤ B) : ∀ p ∈ parents, Cover (WeightedBound B) p := by
  intro p hp
  simp only [parents,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl
  · exact Q0RosterConsume.liftCover (Nat.le_trans (by decide : 242 ≤ 4663) hB) BB6.Agent5Raw11Extra84.cover
  · exact Q0RosterConsume.liftCover (Nat.le_trans (by decide : 227 ≤ 4663) hB) BB6.Agent5Raw11Extra131.cover
  · exact Q0RosterConsume.liftCover (Nat.le_trans (by decide : 98 ≤ 4663) hB) BB6.Agent5Raw11Extra133.cover
  · exact Q0RosterConsume.liftCover (Nat.le_trans (by decide : 1700 ≤ 4663) hB) BB6.Agent5Raw11Extra134.cover

def remove (frontier : List PartialMachine) := Q0RosterConsume.removeCovered frontier parents

theorem discharge (B : Nat) (hB : 4663 ≤ B) (frontier : List PartialMachine)
    (h : ∀ p ∈ remove frontier, ∀ m, compatible p m → WeightedBound B m) :
    ∀ p ∈ frontier, ∀ m, compatible p m → WeightedBound B m :=
  Q0RosterConsume.consume B frontier parents (covers B hB) h

def codes := parents.map tableCode

def remaining := remove BB6.Agent47Raw11Q0Held156.remaining

theorem codes_nodup : codes.Nodup := by decide +kernel
theorem codes_in_remaining : ∀ c ∈ codes, c ∈ BB6.Agent47Raw11Q0Held156.remaining.map tableCode := by decide +kernel
theorem remaining_exact : remaining.map tableCode =
    (BB6.Agent47Raw11Q0Held156.remaining.map tableCode).filter (fun c => !(codes.contains c)) := by decide +kernel
theorem remaining_census : (BB6.Agent47Raw11Route.fullRoster.length, remaining.length) = (299,232) := by decide +kernel
theorem cover_from_remaining (B : Nat) (hB : 4663 ≤ B)
    (h : ∀ p ∈ remaining, ∀ m, compatible p m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent47Raw11Route.parent :=
  BB6.Agent47Raw11Q0Held156.cover_from_remaining B hB (discharge B hB _ h)

#print axioms covers
#print axioms codes_in_remaining
#print axioms remaining_exact
#print axioms remaining_census
#print axioms cover_from_remaining
end BB6.Agent47Raw11FourExtra
