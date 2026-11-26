import Raw11Route
import Root39Lean
import Q0RosterConsume

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47Raw11Root39Consume

open BB6Coverage BB6.Agent13BlankDelay

/-- Exact table code of the already checked q0 active root 39. -/
def root39Code : Nat := 27873199888850548

/-- Remove only the exact root-39 cylinder from the accepted Raw11 residual
    roster. All other pending cylinders are retained verbatim. -/
def remaining : List PartialMachine :=
  Q0RosterConsume.removeCovered BB6.Agent47Raw11Route.remaining
    [BB6.Agent47Root39.parent]

def remainingCodes : List Nat :=
  BB6.Agent47Raw11Route.remainingCodes.filter (fun c => c != root39Code)

def consumedCodes : List Nat :=
  BB6.Agent47Raw11Route.consumedCodes ++ [root39Code]

theorem root39_table_code :
    BB6.Agent47PhaseFrontier.tableCode BB6.Agent47Root39.parent = root39Code := by
  decide +kernel

theorem root39_is_in_raw_remaining :
    BB6.Agent47Raw11Route.remaining.any
      (fun p => Q0ExhaustiveTree.sameTable p BB6.Agent47Root39.parent) = true := by
  decide +kernel

theorem root39_is_removed :
    remaining.any
      (fun p => Q0ExhaustiveTree.sameTable p BB6.Agent47Root39.parent) = false := by
  decide +kernel

theorem remaining_exact :
    remaining.map BB6.Agent47PhaseFrontier.tableCode = remainingCodes := by
  decide +kernel

theorem remaining_census :
    (BB6.Agent47Raw11Route.fullRoster.length, remaining.length) = (299, 293) := by
  decide +kernel

theorem remaining_partition :
    ((BB6.Agent47Raw11Route.checkpointCodes.filter
        (fun c => !(consumedCodes.contains c))) ++ BB6.Agent47Raw11Route.extraCodes).all
        (fun c => remainingCodes.contains c) = true ∧
    remainingCodes.all
        (fun c => ((BB6.Agent47Raw11Route.checkpointCodes.filter
          (fun c => !(consumedCodes.contains c))) ++ BB6.Agent47Raw11Route.extraCodes).contains c) = true := by
  decide +kernel

/-- The Raw11 parent Cover now needs only the 293 residual cylinders:
    root39 is discharged by its exact local Cover at bound 144, lifted to B.
    The remaining assumptions are precisely the original Raw11 route's
    residual list with the root39 table removed. -/
theorem cover_from_remaining (B : Nat) (hB : 234 ≤ B)
    (h : ∀ p ∈ remaining, ∀ m, compatible p m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent47Raw11Route.parent := by
  have h144B : 144 ≤ B := Nat.le_trans (by decide) hB
  have hroot39 : Cover (WeightedBound B) BB6.Agent47Root39.parent :=
    Q0RosterConsume.liftCover h144B BB6.Agent47Root39.cover
  have hraw : ∀ p ∈ BB6.Agent47Raw11Route.remaining,
      ∀ m, compatible p m → WeightedBound B m := by
    exact Q0RosterConsume.consume B BB6.Agent47Raw11Route.remaining
      [BB6.Agent47Root39.parent]
      (by
        intro q hq
        simp at hq
        subst q
        exact hroot39)
      h
  exact BB6.Agent47Raw11Route.cover_from_remaining B hB hraw

#print axioms root39_table_code
#print axioms root39_is_in_raw_remaining
#print axioms root39_is_removed
#print axioms remaining_exact
#print axioms remaining_census
#print axioms remaining_partition
#print axioms cover_from_remaining

end BB6.Agent47Raw11Root39Consume
