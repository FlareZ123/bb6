import Raw11Q0Combined
import Raw11FourExtra

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw11Q0CombinedExtra
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent47PhaseFrontier (tableCode)

def remaining := BB6.Agent47Raw11FourExtra.remove BB6.Agent47Raw11Q0Combined.remaining

theorem codes_in_remaining : ∀ c ∈ BB6.Agent47Raw11FourExtra.codes,
    c ∈ BB6.Agent47Raw11Q0Combined.remaining.map tableCode := by decide +kernel

theorem remaining_census : (BB6.Agent47Raw11Route.fullRoster.length, remaining.length) = (299,152) := by decide +kernel

theorem cover_from_remaining (B : Nat) (hB : 4663 ≤ B)
    (h : ∀ p ∈ remaining, ∀ m, compatible p m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent47Raw11Route.parent :=
  BB6.Agent47Raw11Q0Combined.cover_from_remaining B hB
    (BB6.Agent47Raw11FourExtra.discharge B hB _ h)

#print axioms codes_in_remaining
#print axioms remaining_census
#print axioms cover_from_remaining
end BB6.Agent47Raw11Q0CombinedExtra
