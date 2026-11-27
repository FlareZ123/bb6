import Raw11Q0BankHeld28
import Raw11Q0Held156

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47Raw11Q0Combined
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent47PhaseFrontier (tableCode)

def remaining : List PartialMachine :=
  BB6.Agent47Raw11Q0Held156.remove BB6.Agent47Raw11Q0BankHeld28.remaining

theorem held_count :
    (BB6.Agent47Raw11Q0BankHeld28.remaining.map tableCode).count
      (tableCode BB6.Agent47Raw11Q0Held156.parent) = 1 := by decide +kernel

theorem remaining_census :
    (BB6.Agent47Raw11Route.fullRoster.length, remaining.length) = (299,156) := by decide +kernel

theorem cover_from_remaining (B : Nat) (hB : 4663 ≤ B)
    (h : ∀ p ∈ remaining, ∀ m, compatible p m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent47Raw11Route.parent :=
  BB6.Agent47Raw11Q0BankHeld28.cover_from_remaining B hB
    (BB6.Agent47Raw11Q0Held156.discharge B _ h)

#print axioms held_count
#print axioms remaining_census
#print axioms cover_from_remaining
end BB6.Agent47Raw11Q0Combined
