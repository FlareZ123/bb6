import FastThreeHoleAudit
import WeightedTNF

namespace BB6.Agent3OneHoleFirstQuery
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay

/-!
Any completion of a one-hole six-state table with a uniform exact blank
first-query witness either runs forever (when the hole is filled), or
halts precisely at the witnessed query (when the hole is left undefined).
The only numeric overhead is the standard six-state blank-delay allowance.
No facts about the particular Raw139 leaf are built into this theorem.
-/

/-- A counted original-machine first query plus totality away from that
    slot gives a full weighted Cover of every completion. -/
theorem cover_of_uniform_first_query (p : PartialMachine) (slot : Slot)
    (steps : Nat)
    (hrest : ∀ t, t ≠ slot → ∃ mv, p t = some (some mv))
    (hreach : ∀ m, compatible p m →
      ∃ c, BB6Coverage.run m steps BB6Coverage.blank = some c ∧
        readSlot c = slot) :
    Cover (WeightedBound (steps + 6)) p := by
  apply Cover.leaf
  intro m hm
  cases ht : m slot with
  | some mv =>
    apply weighted_never
    apply all_ordinary_never
    intro t
    by_cases he : t = slot
    · subst t
      exact ⟨mv, ht⟩
    · obtain ⟨u, hu⟩ := hrest t he
      exact ⟨u, hm t _ hu⟩
  | none =>
    obtain ⟨c, hc, hslot⟩ := hreach m hm
    have hh : HaltsAfter m steps := by
      constructor
      · change (BB6Coverage.run m steps BB6Coverage.blank).isSome = true
        rw [hc]
        rfl
      · change (BB6Coverage.run m steps BB6Coverage.blank).bind (rawStep m) = none
        rw [hc]
        simp [rawStep, hslot, ht]
    intro k delay hk hdelay
    have he := halting_time_unique m k steps hk hh
    have hlt : delay < 6 := List.mem_range.mp (List.mem_filter.mp hdelay).1
    omega

#print axioms cover_of_uniform_first_query
end BB6.Agent3OneHoleFirstQuery
