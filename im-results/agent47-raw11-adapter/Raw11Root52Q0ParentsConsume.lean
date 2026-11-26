import Raw11Root52ExtrasConsume
import Root33Lean
import Root49Lean
import Root51Lean
import Q0RosterConsume

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47Raw11Root52Q0ParentsConsume

open BB6Coverage BB6.Agent13BlankDelay

/-- Three additional q0 checkpoint parents with complete local Covers. -/
def q0Parents : List PartialMachine := [
  BB6.Agent47Root33.parent,
  BB6.Agent47Root49.parent,
  BB6.Agent47Root51.parent
]

def q0Codes : List Nat :=
  q0Parents.map BB6.Agent47PhaseFrontier.tableCode

def expectedQ0Codes : List Nat :=
  [27873199888846492, 27873199888857308, 27873199888858660]

def remaining : List PartialMachine :=
  Q0RosterConsume.removeCovered BB6.Agent47Raw11Root52ExtrasConsume.remaining q0Parents

def consumedCodes : List Nat :=
  BB6.Agent47Raw11Root52ExtrasConsume.consumedCodes ++ q0Codes

def remainingCodes : List Nat :=
  BB6.Agent47Raw11Root52ExtrasConsume.remainingCodes.filter
    (fun c => !(q0Codes.contains c))

def q0Covers (B : Nat) (hB : 4663 ≤ B) :
    List (PSigma fun p : PartialMachine => Cover (WeightedBound B) p) := [
  ⟨BB6.Agent47Root33.parent,
    Q0RosterConsume.liftCover (A := 162) (B := B) (Nat.le_trans (by decide : 162 ≤ 4663) hB) BB6.Agent47Root33.cover⟩,
  ⟨BB6.Agent47Root49.parent,
    Q0RosterConsume.liftCover (A := 234) (B := B) (Nat.le_trans (by decide : 234 ≤ 4663) hB) BB6.Agent47Root49.cover⟩,
  ⟨BB6.Agent47Root51.parent,
    Q0RosterConsume.liftCover (A := 208) (B := B) (Nat.le_trans (by decide : 208 ≤ 4663) hB) BB6.Agent47Root51.cover⟩
]

theorem q0Covers_tables (B : Nat) (hB : 4663 ≤ B) :
    (q0Covers B hB).map PSigma.fst = q0Parents := by
  rfl

theorem covers (B : Nat) (hB : 4663 ≤ B) :
    ∀ p ∈ q0Parents, Cover (WeightedBound B) p := by
  intro p hp
  have hp' : p ∈ (q0Covers B hB).map PSigma.fst := by
    rw [q0Covers_tables]
    exact hp
  rcases List.mem_map.mp hp' with ⟨⟨q, hq⟩, hqmem, hEq⟩
  cases hEq
  exact hq

theorem q0_codes_exact : q0Codes = expectedQ0Codes := by
  decide +kernel

theorem q0_codes_nodup : q0Codes.Nodup := by
  decide +kernel

theorem q0_codes_subset_checkpoint :
    ∀ c ∈ q0Codes, c ∈ BB6.Agent47Raw11Route.checkpointCodes := by
  decide +kernel

theorem remaining_exact :
    remaining.map BB6.Agent47PhaseFrontier.tableCode = remainingCodes := by
  decide +kernel

theorem remaining_codes_after_extras :
    remainingCodes =
      BB6.Agent47Raw11Root52ExtrasConsume.remainingCodes.filter
        (fun c => !(q0Codes.contains c)) := by
  rfl

theorem remaining_census :
    (BB6.Agent47Raw11Route.fullRoster.length, remaining.length) = (299, 243) := by
  decide +kernel

/-- Consume q0 parents 33, 49 and 51 after the accepted root39/root52 and
    46-extra Covers. Their bounds (162, 234, 208) all lift under B >= 4663. -/
theorem cover_from_remaining (B : Nat) (hB : 4663 ≤ B)
    (h : ∀ p ∈ remaining, ∀ m, compatible p m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent47Raw11Route.parent := by
  have hAfterQ0 :
      ∀ p ∈ BB6.Agent47Raw11Root52ExtrasConsume.remaining,
        ∀ m, compatible p m → WeightedBound B m := by
    exact Q0RosterConsume.consume B
      BB6.Agent47Raw11Root52ExtrasConsume.remaining q0Parents
      (covers B hB) h
  exact BB6.Agent47Raw11Root52ExtrasConsume.cover_from_remaining B hB hAfterQ0

#print axioms q0Covers_tables
#print axioms covers
#print axioms q0_codes_exact
#print axioms q0_codes_nodup
#print axioms q0_codes_subset_checkpoint
#print axioms remaining_exact
#print axioms remaining_codes_after_extras
#print axioms remaining_census
#print axioms cover_from_remaining

end BB6.Agent47Raw11Root52Q0ParentsConsume
