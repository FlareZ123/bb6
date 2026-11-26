import Raw11Root39Consume
import Q0Root52Parent
import Q0RosterConsume

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47Raw11Root52Consume

open BB6Coverage BB6.Agent13BlankDelay

/-- Exact base-26 table code of q0 active root 52. -/
def root52Code : Nat := 27873408715923912

/-- Remove only root52 from the root39-reduced Raw11 frontier. -/
def remaining : List PartialMachine :=
  Q0RosterConsume.removeCovered BB6.Agent47Raw11Root39Consume.remaining
    [Q0Root52.rootParent]

def remainingCodes : List Nat :=
  BB6.Agent47Raw11Root39Consume.remainingCodes.filter (fun c => c != root52Code)

def consumedCodes : List Nat :=
  BB6.Agent47Raw11Root39Consume.consumedCodes ++ [root52Code]

theorem root52_table_code :
    BB6.Agent47PhaseFrontier.tableCode Q0Root52.rootParent = root52Code := by
  decide +kernel

theorem root52_is_in_raw_remaining :
    BB6.Agent47Raw11Root39Consume.remaining.any
      (fun p => Q0ExhaustiveTree.sameTable p Q0Root52.rootParent) = true := by
  decide +kernel

theorem root52_is_removed :
    remaining.any
      (fun p => Q0ExhaustiveTree.sameTable p Q0Root52.rootParent) = false := by
  decide +kernel

theorem remaining_exact :
    remaining.map BB6.Agent47PhaseFrontier.tableCode = remainingCodes := by
  decide +kernel

theorem remaining_census :
    (BB6.Agent47Raw11Route.fullRoster.length, remaining.length) = (299, 292) := by
  decide +kernel

theorem remaining_partition :
    ((BB6.Agent47Raw11Route.checkpointCodes.filter
        (fun c => !(consumedCodes.contains c))) ++ BB6.Agent47Raw11Route.extraCodes).all
        (fun c => remainingCodes.contains c) = true ∧
    remainingCodes.all
        (fun c => ((BB6.Agent47Raw11Route.checkpointCodes.filter
          (fun c => !(consumedCodes.contains c))) ++ BB6.Agent47Raw11Route.extraCodes).contains c) = true := by
  decide +kernel

/-- Consume root52's independently kernel-checked bound-4663 Cover after
    root39, leaving exactly 292 Raw11 residual cylinders. -/
theorem cover_from_remaining (B : Nat) (hB : 4663 ≤ B)
    (h : ∀ p ∈ remaining, ∀ m, compatible p m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent47Raw11Route.parent := by
  have hAfter39 : ∀ p ∈ BB6.Agent47Raw11Root39Consume.remaining,
      ∀ m, compatible p m → WeightedBound B m := by
    exact Q0RosterConsume.consume B BB6.Agent47Raw11Root39Consume.remaining
      [Q0Root52.rootParent]
      (by
        intro q hq
        simp at hq
        subst q
        exact Q0RosterConsume.liftCover hB Q0Root52.safe_root)
      h
  exact BB6.Agent47Raw11Root39Consume.cover_from_remaining B
    (Nat.le_trans (by decide) hB) hAfter39

#print axioms root52_table_code
#print axioms root52_is_in_raw_remaining
#print axioms root52_is_removed
#print axioms remaining_exact
#print axioms remaining_census
#print axioms remaining_partition
#print axioms cover_from_remaining

end BB6.Agent47Raw11Root52Consume
