import Raw139C1OneLACover
import Raw139C1OneLBCover
import Raw139C1OneLFCover
import Raw139C1OneRACover
import Raw139C1OneRBCover
import Raw139C1OneRFCover
import Raw139C1ZeroLBCover
import Raw139C1ZeroLFCover
import Raw139C1ZeroRBCover
import Raw139C1ZeroRCCover
import Raw139C1Direct

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent48Raw139C1Batch
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay

/-- The twelve exact C/1 siblings; the champion C/1=0RF child is absent. -/
def parents : List PartialMachine := [
  fromCodes [7,24,11,24,14,2,3,16,12,11,24,24],
  fromCodes [7,24,11,24,14,6,3,16,12,11,24,24],
  fromCodes [7,24,11,24,14,22,3,16,12,11,24,24],
  fromCodes [7,24,11,24,14,3,3,16,12,11,24,24],
  fromCodes [7,24,11,24,14,7,3,16,12,11,24,24],
  fromCodes [7,24,11,24,14,23,3,16,12,11,24,24],
  fromCodes [7,24,11,24,14,4,3,16,12,11,24,24],
  fromCodes [7,24,11,24,14,20,3,16,12,11,24,24],
  fromCodes [7,24,11,24,14,5,3,16,12,11,24,24],
  fromCodes [7,24,11,24,14,9,3,16,12,11,24,24],
  fromCodes [7,24,11,24,14,11,3,16,12,11,24,24],
  fromCodes [7,24,11,24,14,19,3,16,12,11,24,24]]

/-- The literal table inventory is definitionally the producer inventory. -/
theorem parents_eq : parents = [
  BB6.Agent48Raw139C1OneLA.parent,
  BB6.Agent48Raw139C1OneLB.parent,
  BB6.Agent48Raw139C1OneLF.parent,
  BB6.Agent48Raw139C1OneRA.parent,
  BB6.Agent48Raw139C1OneRB.parent,
  BB6.Agent48Raw139C1OneRF.parent,
  BB6.Agent48Raw139C1ZeroLB.parent,
  BB6.Agent48Raw139C1ZeroLF.parent,
  BB6.Agent48Raw139C1ZeroRB.parent,
  BB6.Agent48Raw139C1ZeroRC.parent,
  BB6.Agent48Raw139C1.OneRC.parent,
  BB6.Agent48Raw139C1.OneRE.parent] := rfl

/-- Every compatible completion of each of the twelve cylinders has weighted
    halting score at most 2511. This is a semantic parent contract. -/
theorem all_completions_weighted (p : PartialMachine) (hp : p ∈ parents) :
    ∀ m, compatible p m → WeightedBound 2511 m := by
  simp only [parents, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro m hm k d hk hd
    exact Nat.le_trans
      (BB6.Agent48Raw139C1OneLA.all_completions_weighted m hm k d hk hd)
      (by decide : 533 ≤ 2511)
  · intro m hm k d hk hd
    exact Nat.le_trans
      (BB6.Agent48Raw139C1OneLB.all_completions_weighted m hm k d hk hd)
      (by decide : 712 ≤ 2511)
  · intro m hm k d hk hd
    exact Nat.le_trans
      (BB6.Agent48Raw139C1OneLF.all_completions_weighted m hm k d hk hd)
      (by decide : 232 ≤ 2511)
  · intro m hm k d hk hd
    exact Nat.le_trans
      (BB6.Agent48Raw139C1OneRA.all_completions_weighted m hm k d hk hd)
      (by decide : 725 ≤ 2511)
  · intro m hm k d hk hd
    exact Nat.le_trans
      (BB6.Agent48Raw139C1OneRB.all_completions_weighted m hm k d hk hd)
      (by decide : 317 ≤ 2511)
  · intro m hm k d hk hd
    exact Nat.le_trans
      (BB6.Agent48Raw139C1OneRF.all_completions_weighted m hm k d hk hd)
      (by decide : 2242 ≤ 2511)
  · intro m hm k d hk hd
    exact Nat.le_trans
      (BB6.Agent48Raw139C1ZeroLB.all_completions_weighted m hm k d hk hd)
      (by decide : 542 ≤ 2511)
  · intro m hm k d hk hd
    exact Nat.le_trans
      (BB6.Agent48Raw139C1ZeroLF.all_completions_weighted m hm k d hk hd)
      (by decide : 683 ≤ 2511)
  · intro m hm k d hk hd
    exact Nat.le_trans
      (BB6.Agent48Raw139C1ZeroRB.all_completions_weighted m hm k d hk hd)
      (by decide : 2511 ≤ 2511)
  · intro m hm k d hk hd
    exact Nat.le_trans
      (BB6.Agent48Raw139C1ZeroRC.all_completions_weighted m hm k d hk hd)
      (by decide : 1853 ≤ 2511)
  · intro m hm k d hk hd
    exact Nat.le_trans
      (BB6.Agent48Raw139C1.OneRC.all_completions_weighted m hm k d hk hd)
      (by decide : 0 ≤ 2511)
  · intro m hm k d hk hd
    exact Nat.le_trans
      (BB6.Agent48Raw139C1.OneRE.all_completions_weighted m hm k d hk hd)
      (by decide : 0 ≤ 2511)

/-- A stable Cover contract, usable at the champion score or any larger bound. -/
theorem cover_at {B : Nat} (hB : 2511 ≤ B)
    (p : PartialMachine) (hp : p ∈ parents) : Cover (WeightedBound B) p :=
  Cover.leaf p (fun m hm k d hk hd =>
    Nat.le_trans (all_completions_weighted p hp m hm k d hk hd) hB)

/-- Remove exactly these physical tables from any existing frontier obligation.
    The retained complement is explicit, so no unrelated entry is discarded. -/
theorem consume {α : Type} {B : Nat} (hB : 2511 ≤ B)
    (roster : List (α × PartialMachine))
    (hLeaves : ∀ e ∈ roster, e.2 ∉ parents → Cover (WeightedBound B) e.2) :
    ∀ e ∈ roster, Cover (WeightedBound B) e.2 := by
  intro e he
  by_cases hp : e.2 ∈ parents
  · exact cover_at hB e.2 hp
  · exact hLeaves e he hp

#print axioms parents_eq
#print axioms all_completions_weighted
#print axioms cover_at
#print axioms consume
end BB6.Agent48Raw139C1Batch
