import CanonicalRosterRefinement

namespace BB6.Agent42FrontierCount

open BB6.Agent13BlankDelay
open BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalRefinement

abbrev Entry := List Move × PartialMachine

/-- Count the exact parents selected by the table-equality graft. -/
def graftMatchCount (p : PartialMachine) (roster : List Entry) : Nat :=
  (roster.filter (fun e => sameTable e.2 p)).length

/-- Structural length accounting for graftRoster. The additive form avoids
    nonlinear Nat subtraction and is stable under large function-valued
    rosters. -/
theorem graftRoster_length_add_count (p : PartialMachine)
    (replacement roster : List Entry) :
    (graftRoster p replacement roster).length +
        graftMatchCount p roster =
      roster.length + graftMatchCount p roster * replacement.length := by
  induction roster with
  | nil =>
      simp [graftRoster,graftMatchCount]
  | cons e es ih =>
      by_cases h : sameTable e.2 p = true
      · simp [graftRoster,graftEntry,graftMatchCount,h,ih,
          Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      · simp [graftRoster,graftEntry,graftMatchCount,h,ih,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem graftRoster_length_of_one (p : PartialMachine)
    (replacement roster : List Entry)
    (hcount : graftMatchCount p roster = 1) :
    (graftRoster p replacement roster).length + 1 =
      roster.length + replacement.length := by
  simpa [graftMatchCount,hcount] using
    (graftRoster_length_add_count p replacement roster)

/-- Equality-based list replacement, used by Agent48's packed-table graft. -/
def replaceList {α : Type} [DecidableEq α] (target : α)
    (replacement roster : List α) : List α :=
  roster.flatMap fun x => if x = target then replacement else [x]

/-- Number of exact target occurrences consumed by replaceList. -/
def replaceListMatchCount {α : Type} [DecidableEq α]
    (target : α) (roster : List α) : Nat :=
  (roster.filter fun x => decide (x = target)).length

/-- Additive length identity for equality-based replacement. -/
theorem replaceList_length_add_count {α : Type} [DecidableEq α]
    (target : α) (replacement roster : List α) :
    (replaceList target replacement roster).length +
        replaceListMatchCount target roster =
      roster.length + replaceListMatchCount target roster * replacement.length := by
  induction roster with
  | nil =>
      simp [replaceList, replaceListMatchCount]
  | cons x xs ih =>
      by_cases h : x = target
      · subst x
        have hlen :
            (replaceList target replacement (target :: xs)).length =
              replacement.length + (replaceList target replacement xs).length := by
          simp [replaceList]
        have hcount :
            replaceListMatchCount target (target :: xs) =
              1 + replaceListMatchCount target xs := by
          simp [replaceListMatchCount]
        rw [hlen, hcount, List.length_cons, ih]
        simp [Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      · have hlen :
            (replaceList target replacement (x :: xs)).length =
              1 + (replaceList target replacement xs).length := by
          simp [replaceList, h]
        have hcount :
            replaceListMatchCount target (x :: xs) =
              replaceListMatchCount target xs := by
          simp [replaceListMatchCount, h]
        rw [hlen, hcount, List.length_cons, ih]
        simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Exact one-parent replacement length, without evaluating the resulting list. -/
theorem replaceList_length_of_one {α : Type} [DecidableEq α]
    (target : α) (replacement roster : List α)
    (hcount : replaceListMatchCount target roster = 1) :
    (replaceList target replacement roster).length + 1 =
      roster.length + replacement.length := by
  simpa [replaceListMatchCount, hcount] using
    (replaceList_length_add_count target replacement roster)

#print axioms graftRoster_length_add_count
#print axioms graftRoster_length_of_one

end BB6.Agent42FrontierCount
