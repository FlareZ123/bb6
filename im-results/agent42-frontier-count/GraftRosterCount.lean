import CanonicalRosterRefinement

namespace BB6.Agent42FrontierCount

open BB6.Agent13BlankDelay
open BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalRefinement

abbrev Entry := List Move × PartialMachine

/-- Count the exact parents selected by the table-equality graft. -/
def graftMatchCount (p : PartialMachine) (roster : List Entry) : Nat :=
  (roster.filter (fun e => sameTable e.2 p)).length

/-- One-step unfolding of the roster graft, keeping the tail opaque. -/
theorem graftRoster_cons (p : PartialMachine) (replacement : List Entry)
    (e : Entry) (es : List Entry) :
    graftRoster p replacement (e :: es) =
      graftEntry p replacement e ++ graftRoster p replacement es := by
  rfl

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
      simp [graftRoster, graftMatchCount]
  | cons e es ih =>
      by_cases h : sameTable e.2 p = true
      · have hlen :
            (graftRoster p replacement (e :: es)).length =
              replacement.length + (graftRoster p replacement es).length := by
          rw [graftRoster_cons]
          simp [graftEntry, h]
        have hcount : graftMatchCount p (e :: es) =
            1 + graftMatchCount p es := by
          simp [graftMatchCount, h, Nat.add_comm]
        rw [hlen, hcount, List.length_cons]
        calc
          replacement.length + (graftRoster p replacement es).length +
              (1 + graftMatchCount p es) =
            ((graftRoster p replacement es).length + graftMatchCount p es) +
              (1 + replacement.length) := by omega
          _ = (es.length + graftMatchCount p es * replacement.length) +
              (1 + replacement.length) := by rw [ih]
          _ = es.length + 1 + (1 + graftMatchCount p es) * replacement.length := by
              simp [Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      · have hlen :
            (graftRoster p replacement (e :: es)).length =
              1 + (graftRoster p replacement es).length := by
          rw [graftRoster_cons]
          simp [graftEntry, h]
          exact Nat.add_comm _ _
        have hcount : graftMatchCount p (e :: es) =
            graftMatchCount p es := by
          simp [graftMatchCount, h]
        rw [hlen, hcount, List.length_cons]
        calc
          1 + (graftRoster p replacement es).length + graftMatchCount p es =
            ((graftRoster p replacement es).length + graftMatchCount p es) + 1 := by omega
          _ = (es.length + graftMatchCount p es * replacement.length) + 1 := by rw [ih]
          _ = es.length + 1 + graftMatchCount p es * replacement.length := by omega

theorem graftRoster_length_of_one (p : PartialMachine)
    (replacement roster : List Entry)
    (hcount : graftMatchCount p roster = 1) :
    (graftRoster p replacement roster).length + 1 =
      roster.length + replacement.length := by
  simpa [graftMatchCount, hcount] using
    (graftRoster_length_add_count p replacement roster)

/-- Equality-based list replacement, used by Agent48's packed-table graft. -/
def replaceList {α : Type} [DecidableEq α] (target : α)
    (replacement roster : List α) : List α :=
  roster.flatMap fun x => if x = target then replacement else [x]

/-- Number of exact target occurrences consumed by replaceList. -/
def replaceListMatchCount {α : Type} [DecidableEq α]
    (target : α) (roster : List α) : Nat :=
  (roster.filter fun x => decide (x = target)).length

/-- One-step unfolding of equality-based replacement, keeping the tail opaque. -/
theorem replaceList_cons {α : Type} [DecidableEq α] (target : α)
    (replacement : List α) (x : α) (xs : List α) :
    replaceList target replacement (x :: xs) =
      (if x = target then replacement else [x]) ++
        replaceList target replacement xs := by
  rfl

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
          rw [replaceList_cons]
          simp
        have hcount : replaceListMatchCount target (target :: xs) =
            1 + replaceListMatchCount target xs := by
          simp [replaceListMatchCount, Nat.add_comm]
        rw [hlen, hcount, List.length_cons]
        calc
          replacement.length + (replaceList target replacement xs).length +
              (1 + replaceListMatchCount target xs) =
            ((replaceList target replacement xs).length + replaceListMatchCount target xs) +
              (1 + replacement.length) := by omega
          _ = (xs.length + replaceListMatchCount target xs * replacement.length) +
              (1 + replacement.length) := by rw [ih]
          _ = xs.length + 1 + (1 + replaceListMatchCount target xs) * replacement.length := by
              simp [Nat.add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      · have hlen :
            (replaceList target replacement (x :: xs)).length =
              1 + (replaceList target replacement xs).length := by
          rw [replaceList_cons]
          simp [h]
          exact Nat.add_comm _ _
        have hcount : replaceListMatchCount target (x :: xs) =
            replaceListMatchCount target xs := by
          simp [replaceListMatchCount, h]
        rw [hlen, hcount, List.length_cons]
        calc
          1 + (replaceList target replacement xs).length +
              replaceListMatchCount target xs =
            ((replaceList target replacement xs).length + replaceListMatchCount target xs) +
              1 := by omega
          _ = (xs.length + replaceListMatchCount target xs * replacement.length) + 1 := by rw [ih]
          _ = xs.length + 1 + replaceListMatchCount target xs * replacement.length := by omega

/-- Exact one-parent replacement length, without evaluating the resulting list. -/
theorem replaceList_length_of_one {α : Type} [DecidableEq α]
    (target : α) (replacement roster : List α)
    (hcount : replaceListMatchCount target roster = 1) :
    (replaceList target replacement roster).length + 1 =
      roster.length + replacement.length := by
  have h := replaceList_length_add_count target replacement roster
  rw [hcount] at h
  simpa using h

#print axioms graftRoster_length_add_count
#print axioms graftRoster_length_of_one

end BB6.Agent42FrontierCount
