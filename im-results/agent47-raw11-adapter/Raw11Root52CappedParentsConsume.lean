import Raw11Root52Q0ParentsConsume
import Agent5Raw11Extra126
import Agent5Raw11Extra127
import Agent5Raw11Extra128
import Agent5Raw11Extra129
import Agent5Raw11Extra130
import Agent5Raw11Extra137
import Q0RosterConsume

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47Raw11Root52CappedParentsConsume

open BB6Coverage BB6.Agent13BlankDelay

/-- Six independently source-accepted five/six-hole parent Covers beyond the
    46-extra and three-q0 consumer. -/
def cappedParents : List PartialMachine := [
  BB6.Agent5Raw11Extra126.parent,
  BB6.Agent5Raw11Extra127.parent,
  BB6.Agent5Raw11Extra128.parent,
  BB6.Agent5Raw11Extra129.parent,
  BB6.Agent5Raw11Extra130.parent,
  BB6.Agent5Raw11Extra137.parent
]

def cappedCodes : List Nat :=
  cappedParents.map BB6.Agent47PhaseFrontier.tableCode

/-- Exact residual frontier after the accepted 46-extra/q0 consumer and
    these six additional parent Covers. -/
def remaining : List PartialMachine :=
  Q0RosterConsume.removeCovered BB6.Agent47Raw11Root52Q0ParentsConsume.remaining cappedParents

def consumedCodes : List Nat :=
  BB6.Agent47Raw11Root52Q0ParentsConsume.consumedCodes ++ cappedCodes

def remainingCodes : List Nat :=
  BB6.Agent47Raw11Root52Q0ParentsConsume.remainingCodes.filter
    (fun c => !(cappedCodes.contains c))

def cappedCovers (B : Nat) (hB : 4663 ≤ B) :
    List (PSigma fun p : PartialMachine => Cover (WeightedBound B) p) := [
  ⟨BB6.Agent5Raw11Extra126.parent,
    Q0RosterConsume.liftCover (A := 167) (B := B) (Nat.le_trans (by decide : 167 ≤ 4663) hB) BB6.Agent5Raw11Extra126.cover⟩,
  ⟨BB6.Agent5Raw11Extra127.parent,
    Q0RosterConsume.liftCover (A := 168) (B := B) (Nat.le_trans (by decide : 168 ≤ 4663) hB) BB6.Agent5Raw11Extra127.cover⟩,
  ⟨BB6.Agent5Raw11Extra128.parent,
    Q0RosterConsume.liftCover (A := 125) (B := B) (Nat.le_trans (by decide : 125 ≤ 4663) hB) BB6.Agent5Raw11Extra128.cover⟩,
  ⟨BB6.Agent5Raw11Extra129.parent,
    Q0RosterConsume.liftCover (A := 214) (B := B) (Nat.le_trans (by decide : 214 ≤ 4663) hB) BB6.Agent5Raw11Extra129.cover⟩,
  ⟨BB6.Agent5Raw11Extra130.parent,
    Q0RosterConsume.liftCover (A := 131) (B := B) (Nat.le_trans (by decide : 131 ≤ 4663) hB) BB6.Agent5Raw11Extra130.cover⟩,
  ⟨BB6.Agent5Raw11Extra137.parent,
    Q0RosterConsume.liftCover (A := 180) (B := B) (Nat.le_trans (by decide : 180 ≤ 4663) hB) BB6.Agent5Raw11Extra137.cover⟩
]

theorem cappedCovers_tables (B : Nat) (hB : 4663 ≤ B) :
    (cappedCovers B hB).map PSigma.fst = cappedParents := by
  rfl

theorem covers (B : Nat) (hB : 4663 ≤ B) :
    ∀ p ∈ cappedParents, Cover (WeightedBound B) p := by
  intro p hp
  have hp' : p ∈ (cappedCovers B hB).map PSigma.fst := by
    rw [cappedCovers_tables]
    exact hp
  rcases List.mem_map.mp hp' with ⟨⟨q, hq⟩, hqmem, hEq⟩
  cases hEq
  exact hq

theorem capped_codes_nodup : cappedCodes.Nodup := by
  decide +kernel

theorem capped_codes_subset_extra :
    ∀ c ∈ cappedCodes, c ∈ BB6.Agent47Raw11Route.extraCodes := by
  decide +kernel

theorem remaining_exact :
    remaining.map BB6.Agent47PhaseFrontier.tableCode = remainingCodes := by
  decide +kernel

theorem remaining_codes_after_q0 :
    remainingCodes =
      BB6.Agent47Raw11Root52Q0ParentsConsume.remainingCodes.filter
        (fun c => !(cappedCodes.contains c)) := by
  rfl

theorem remaining_census :
    (BB6.Agent47Raw11Route.fullRoster.length, remaining.length) = (299, 237) := by
  decide +kernel

/-- Consume six more independently checked Raw11 parent Covers after the
    46-extra and three q0 parent Covers. -/
theorem cover_from_remaining (B : Nat) (hB : 4663 ≤ B)
    (h : ∀ p ∈ remaining, ∀ m, compatible p m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent47Raw11Route.parent := by
  have hAfterCapped :
      ∀ p ∈ BB6.Agent47Raw11Root52Q0ParentsConsume.remaining,
        ∀ m, compatible p m → WeightedBound B m := by
    exact Q0RosterConsume.consume B
      BB6.Agent47Raw11Root52Q0ParentsConsume.remaining cappedParents
      (covers B hB) h
  exact BB6.Agent47Raw11Root52Q0ParentsConsume.cover_from_remaining B hB hAfterCapped

#print axioms cappedCovers_tables
#print axioms covers
#print axioms capped_codes_nodup
#print axioms capped_codes_subset_extra
#print axioms remaining_exact
#print axioms remaining_codes_after_q0
#print axioms remaining_census
#print axioms cover_from_remaining

end BB6.Agent47Raw11Root52CappedParentsConsume
