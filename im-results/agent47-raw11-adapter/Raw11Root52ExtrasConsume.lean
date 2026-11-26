import Raw11Root52Consume
import Raw11ExtraSmall
import Raw11Extra91
import Raw11Extra92
import Raw11Extra123
import Raw11Extra124
import Q0RosterConsume

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47Raw11Root52ExtrasConsume

open BB6Coverage BB6.Agent13BlankDelay

/-- The 35 checked Raw11-extra parent tables. Two new parents use exact growing-return leaf Covers. -/
def closedTables : List PartialMachine := [
  BB6.Agent47Extra91.parent,
  BB6.Agent47Extra92.parent,
  BB6.Agent47Extra93.parent,
  BB6.Agent47Extra94.parent,
  BB6.Agent47Extra95.parent,
  BB6.Agent47Extra96.parent,
  BB6.Agent47Extra97.parent,
  BB6.Agent47Extra98.parent,
  BB6.Agent47Extra99.parent,
  BB6.Agent47Extra100.parent,
  BB6.Agent47Extra101.parent,
  BB6.Agent47Extra102.parent,
  BB6.Agent47Extra103.parent,
  BB6.Agent47Extra104.parent,
  BB6.Agent47Extra105.parent,
  BB6.Agent47Extra106.parent,
  BB6.Agent47Extra107.parent,
  BB6.Agent47Extra108.parent,
  BB6.Agent47Extra109.parent,
  BB6.Agent47Extra110.parent,
  BB6.Agent47Extra111.parent,
  BB6.Agent47Extra112.parent,
  BB6.Agent47Extra113.parent,
  BB6.Agent47Extra114.parent,
  BB6.Agent47Extra115.parent,
  BB6.Agent47Extra116.parent,
  BB6.Agent47Extra117.parent,
  BB6.Agent47Extra118.parent,
  BB6.Agent47Extra119.parent,
  BB6.Agent47Extra120.parent,
  BB6.Agent47Extra121.parent,
  BB6.Agent47Extra122.parent,
  BB6.Agent47Extra123.parent,
  BB6.Agent47Extra124.parent,
  BB6.Agent47Extra141.parent
]

def closedCodes : List Nat :=
  closedTables.map BB6.Agent47PhaseFrontier.tableCode

/-- Exact residual frontier after root39, root52, and all 35 completed extra Covers. -/
def remaining : List PartialMachine :=
  Q0RosterConsume.removeCovered BB6.Agent47Raw11Root52Consume.remaining closedTables

def consumedCodes : List Nat :=
  BB6.Agent47Raw11Root52Consume.consumedCodes ++ closedCodes

def remainingCodes : List Nat :=
  BB6.Agent47Raw11Root52Consume.remainingCodes.filter
    (fun c => !(closedCodes.contains c))

/-- Package each exact parent together with its independently checked local Cover. -/
def closedCovers (B : Nat) (hB : 4663 ≤ B) :
    List (PSigma fun p : PartialMachine => Cover (WeightedBound B) p) := [
  ⟨BB6.Agent47Extra91.parent, Q0RosterConsume.liftCover (A := 143) (B := B) (Nat.le_trans (by decide : 143 ≤ 4663) hB) BB6.Agent47Extra91.cover⟩,
  ⟨BB6.Agent47Extra92.parent, Q0RosterConsume.liftCover (A := BB6.Agent47Extra92.bound) (B := B) (Nat.le_trans (by decide : BB6.Agent47Extra92.bound ≤ 4663) hB) BB6.Agent47Extra92.cover⟩,
  ⟨BB6.Agent47Extra93.parent, Q0RosterConsume.liftCover (A := 24) (B := B) (Nat.le_trans (by decide : 24 ≤ 4663) hB) BB6.Agent47Extra93.cover⟩,
  ⟨BB6.Agent47Extra94.parent, Q0RosterConsume.liftCover (A := 30) (B := B) (Nat.le_trans (by decide : 30 ≤ 4663) hB) BB6.Agent47Extra94.cover⟩,
  ⟨BB6.Agent47Extra95.parent, Q0RosterConsume.liftCover (A := 75) (B := B) (Nat.le_trans (by decide : 75 ≤ 4663) hB) BB6.Agent47Extra95.cover⟩,
  ⟨BB6.Agent47Extra96.parent, Q0RosterConsume.liftCover (A := 58) (B := B) (Nat.le_trans (by decide : 58 ≤ 4663) hB) BB6.Agent47Extra96.cover⟩,
  ⟨BB6.Agent47Extra97.parent, Q0RosterConsume.liftCover (A := 58) (B := B) (Nat.le_trans (by decide : 58 ≤ 4663) hB) BB6.Agent47Extra97.cover⟩,
  ⟨BB6.Agent47Extra98.parent, Q0RosterConsume.liftCover (A := 32) (B := B) (Nat.le_trans (by decide : 32 ≤ 4663) hB) BB6.Agent47Extra98.cover⟩,
  ⟨BB6.Agent47Extra99.parent, Q0RosterConsume.liftCover (A := 25) (B := B) (Nat.le_trans (by decide : 25 ≤ 4663) hB) BB6.Agent47Extra99.cover⟩,
  ⟨BB6.Agent47Extra100.parent, Q0RosterConsume.liftCover (A := 44) (B := B) (Nat.le_trans (by decide : 44 ≤ 4663) hB) BB6.Agent47Extra100.cover⟩,
  ⟨BB6.Agent47Extra101.parent, Q0RosterConsume.liftCover (A := 46) (B := B) (Nat.le_trans (by decide : 46 ≤ 4663) hB) BB6.Agent47Extra101.cover⟩,
  ⟨BB6.Agent47Extra102.parent, Q0RosterConsume.liftCover (A := 42) (B := B) (Nat.le_trans (by decide : 42 ≤ 4663) hB) BB6.Agent47Extra102.cover⟩,
  ⟨BB6.Agent47Extra103.parent, Q0RosterConsume.liftCover (A := 42) (B := B) (Nat.le_trans (by decide : 42 ≤ 4663) hB) BB6.Agent47Extra103.cover⟩,
  ⟨BB6.Agent47Extra104.parent, Q0RosterConsume.liftCover (A := 42) (B := B) (Nat.le_trans (by decide : 42 ≤ 4663) hB) BB6.Agent47Extra104.cover⟩,
  ⟨BB6.Agent47Extra105.parent, Q0RosterConsume.liftCover (A := 74) (B := B) (Nat.le_trans (by decide : 74 ≤ 4663) hB) BB6.Agent47Extra105.cover⟩,
  ⟨BB6.Agent47Extra106.parent, Q0RosterConsume.liftCover (A := 62) (B := B) (Nat.le_trans (by decide : 62 ≤ 4663) hB) BB6.Agent47Extra106.cover⟩,
  ⟨BB6.Agent47Extra107.parent, Q0RosterConsume.liftCover (A := 42) (B := B) (Nat.le_trans (by decide : 42 ≤ 4663) hB) BB6.Agent47Extra107.cover⟩,
  ⟨BB6.Agent47Extra108.parent, Q0RosterConsume.liftCover (A := 64) (B := B) (Nat.le_trans (by decide : 64 ≤ 4663) hB) BB6.Agent47Extra108.cover⟩,
  ⟨BB6.Agent47Extra109.parent, Q0RosterConsume.liftCover (A := 127) (B := B) (Nat.le_trans (by decide : 127 ≤ 4663) hB) BB6.Agent47Extra109.cover⟩,
  ⟨BB6.Agent47Extra110.parent, Q0RosterConsume.liftCover (A := 36) (B := B) (Nat.le_trans (by decide : 36 ≤ 4663) hB) BB6.Agent47Extra110.cover⟩,
  ⟨BB6.Agent47Extra111.parent, Q0RosterConsume.liftCover (A := 33) (B := B) (Nat.le_trans (by decide : 33 ≤ 4663) hB) BB6.Agent47Extra111.cover⟩,
  ⟨BB6.Agent47Extra112.parent, Q0RosterConsume.liftCover (A := 36) (B := B) (Nat.le_trans (by decide : 36 ≤ 4663) hB) BB6.Agent47Extra112.cover⟩,
  ⟨BB6.Agent47Extra113.parent, Q0RosterConsume.liftCover (A := 121) (B := B) (Nat.le_trans (by decide : 121 ≤ 4663) hB) BB6.Agent47Extra113.cover⟩,
  ⟨BB6.Agent47Extra114.parent, Q0RosterConsume.liftCover (A := 20) (B := B) (Nat.le_trans (by decide : 20 ≤ 4663) hB) BB6.Agent47Extra114.cover⟩,
  ⟨BB6.Agent47Extra115.parent, Q0RosterConsume.liftCover (A := 54) (B := B) (Nat.le_trans (by decide : 54 ≤ 4663) hB) BB6.Agent47Extra115.cover⟩,
  ⟨BB6.Agent47Extra116.parent, Q0RosterConsume.liftCover (A := 119) (B := B) (Nat.le_trans (by decide : 119 ≤ 4663) hB) BB6.Agent47Extra116.cover⟩,
  ⟨BB6.Agent47Extra117.parent, Q0RosterConsume.liftCover (A := 38) (B := B) (Nat.le_trans (by decide : 38 ≤ 4663) hB) BB6.Agent47Extra117.cover⟩,
  ⟨BB6.Agent47Extra118.parent, Q0RosterConsume.liftCover (A := 74) (B := B) (Nat.le_trans (by decide : 74 ≤ 4663) hB) BB6.Agent47Extra118.cover⟩,
  ⟨BB6.Agent47Extra119.parent, Q0RosterConsume.liftCover (A := 38) (B := B) (Nat.le_trans (by decide : 38 ≤ 4663) hB) BB6.Agent47Extra119.cover⟩,
  ⟨BB6.Agent47Extra120.parent, Q0RosterConsume.liftCover (A := 36) (B := B) (Nat.le_trans (by decide : 36 ≤ 4663) hB) BB6.Agent47Extra120.cover⟩,
  ⟨BB6.Agent47Extra121.parent, Q0RosterConsume.liftCover (A := 141) (B := B) (Nat.le_trans (by decide : 141 ≤ 4663) hB) BB6.Agent47Extra121.cover⟩,
  ⟨BB6.Agent47Extra122.parent, Q0RosterConsume.liftCover (A := 45) (B := B) (Nat.le_trans (by decide : 45 ≤ 4663) hB) BB6.Agent47Extra122.cover⟩,
  ⟨BB6.Agent47Extra123.parent, Q0RosterConsume.liftCover (A := 144) (B := B) (Nat.le_trans (by decide : 144 ≤ 4663) hB) BB6.Agent47Extra123.cover⟩,
  ⟨BB6.Agent47Extra124.parent, Q0RosterConsume.liftCover (A := BB6.Agent47Extra124.bound) (B := B) (Nat.le_trans (by decide : BB6.Agent47Extra124.bound ≤ 4663) hB) BB6.Agent47Extra124.cover⟩,
  ⟨BB6.Agent47Extra141.parent, Q0RosterConsume.liftCover (A := 70) (B := B) (Nat.le_trans (by decide : 70 ≤ 4663) hB) BB6.Agent47Extra141.cover⟩
]

theorem closedCovers_tables (B : Nat) (hB : 4663 ≤ B) :
    (closedCovers B hB).map PSigma.fst = closedTables := by
  rfl

theorem covers (B : Nat) (hB : 4663 ≤ B) :
    ∀ p ∈ closedTables, Cover (WeightedBound B) p := by
  intro p hp
  have hp' : p ∈ (closedCovers B hB).map PSigma.fst := by
    rw [closedCovers_tables]
    exact hp
  rcases List.mem_map.mp hp' with ⟨⟨q, hq⟩, hqmem, hEq⟩
  cases hEq
  exact hq

theorem closed_codes_nodup : closedCodes.Nodup := by
  decide +kernel

theorem closed_codes_subset_extra :
    ∀ c ∈ closedCodes, c ∈ BB6.Agent47Raw11Route.extraCodes := by
  decide +kernel

theorem remaining_exact :
    remaining.map BB6.Agent47PhaseFrontier.tableCode = remainingCodes := by
  decide +kernel

theorem remaining_codes_after_root52 :
    remainingCodes =
      BB6.Agent47Raw11Root52Consume.remainingCodes.filter
        (fun c => !(closedCodes.contains c)) := by
  rfl

theorem remaining_census :
    (BB6.Agent47Raw11Route.fullRoster.length, remaining.length) = (299, 257) := by
  decide +kernel

/-- All 35 local bounds are at most 4663, so each lifts under B >= 4663. -/
theorem cover_from_remaining (B : Nat) (hB : 4663 ≤ B)
    (h : ∀ p ∈ remaining, ∀ m, compatible p m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent47Raw11Route.parent := by
  have hAfterRoot52 :
      ∀ p ∈ BB6.Agent47Raw11Root52Consume.remaining,
        ∀ m, compatible p m → WeightedBound B m := by
    exact Q0RosterConsume.consume B BB6.Agent47Raw11Root52Consume.remaining
      closedTables (covers B hB) h
  exact BB6.Agent47Raw11Root52Consume.cover_from_remaining B hB hAfterRoot52

#print axioms closedCovers_tables
#print axioms covers
#print axioms closed_codes_nodup
#print axioms closed_codes_subset_extra
#print axioms remaining_exact
#print axioms remaining_codes_after_root52
#print axioms remaining_census
#print axioms cover_from_remaining

end BB6.Agent47Raw11Root52ExtrasConsume
