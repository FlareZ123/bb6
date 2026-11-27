import Raw11Q0BankHeld28Part0
import Raw11Q0BankLarge

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw11Q0BankHeld28
open BB6Coverage BB6.Agent13BlankDelay

def closedParents : List PartialMachine := [p28]

theorem covers (B : Nat) (hB : 100 ≤ B) : ∀ p ∈ closedParents, Cover (WeightedBound B) p := by
  intro p hp
  simp only [closedParents,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl
  · exact Q0RosterConsume.liftCover hB cover_p28

def closedCodes : List Nat := closedParents.map BB6.Agent47PhaseFrontier.tableCode
def remaining : List PartialMachine := Q0RosterConsume.removeCovered BB6.Agent47Raw11Q0BankLarge.remaining closedParents
theorem closed_codes_nodup : closedCodes.Nodup := by decide +kernel
theorem closed_codes_in_remaining : ∀ c ∈ closedCodes, c ∈ BB6.Agent47Raw11Q0BankLarge.remaining.map BB6.Agent47PhaseFrontier.tableCode := by decide +kernel
theorem remaining_exact : remaining.map BB6.Agent47PhaseFrontier.tableCode =
    (BB6.Agent47Raw11Q0BankLarge.remaining.map BB6.Agent47PhaseFrontier.tableCode).filter (fun c => !(closedCodes.contains c)) := by decide +kernel
theorem remaining_census : (BB6.Agent47Raw11Route.fullRoster.length, remaining.length) = (299,157) := by decide +kernel
theorem cover_from_remaining (B : Nat) (hB : 4663 ≤ B)
    (h : ∀ p ∈ remaining, ∀ m, compatible p m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent47Raw11Route.parent := by
  exact BB6.Agent47Raw11Q0BankLarge.cover_from_remaining B hB
    (Q0RosterConsume.consume B BB6.Agent47Raw11Q0BankLarge.remaining closedParents
      (covers B (Nat.le_trans (by decide : 100 ≤ 4663) hB)) h)

#print axioms covers
#print axioms closed_codes_in_remaining
#print axioms remaining_exact
#print axioms remaining_census
#print axioms cover_from_remaining
end BB6.Agent47Raw11Q0BankHeld28
