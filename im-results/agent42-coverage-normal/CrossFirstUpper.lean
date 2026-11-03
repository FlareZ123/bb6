import CrossUpper
import TwoFirst

namespace BB6.CoverageAdapter

/-- Standard raw 28-action, six-state BB(6) upper bound iff the restriction
    to two root-normalized A/0 first actions 0RB and 1RB in the canonical
    25-action encoding, with the score-one halt covered by B >= 1.
    The quantifier includes every remaining transition table, with no
    implicit holdout or reachability assumptions. -/
theorem raw_upper_iff_two_first (B : Nat) (hB : 1 ≤ B) :
    (∀ m : BB6.Coverage.RawMachine, ∀ n : Nat,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) n → n ≤ B) ↔
    (∀ m : BB6Coverage.Machine, BB6Coverage.TwoFirst m →
      ∀ n : Nat, BB6Coverage.HaltsAfter m n → n+1 ≤ B) := by
  constructor
  · intro h m _ n hn
    exact ((universal_raw_upper_iff B).mpr h) m n hn
  · intro h
    apply (universal_raw_upper_iff B).mp
    exact BB6Coverage.upper_from_two_first_actions B hB h

/-- Exact BB(6) is reduced to a raw witness plus the two open canonical
    first-transition cylinders. This is a conditional theorem: neither
    the witness nor the remaining universal bound is supplied here. -/
theorem exact_from_two_first_and_raw_witness (B : Nat) (hB : 1 ≤ B)
    (hbound : ∀ m : BB6Coverage.Machine, BB6Coverage.TwoFirst m →
      ∀ n : Nat, BB6Coverage.HaltsAfter m n → n+1 ≤ B)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B := by
  exact ⟨champ, (raw_upper_iff_two_first B hB).mpr hbound⟩

#print axioms raw_upper_iff_two_first
#print axioms exact_from_two_first_and_raw_witness
end BB6.CoverageAdapter
