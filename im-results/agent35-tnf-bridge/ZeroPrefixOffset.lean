import RootShift

namespace BB6Coverage

/-- If a run reaches a translated blank configuration after k ordinary
    moves, every later halting score is shifted by exactly k. This is the
    score-offset bridge needed when a zero-writing prefix is removed before
    normalizing the first nonzero write to the 1RB root. -/
theorem blank_prefix_haltsAt_offset
    (m : Machine) (q q' : Fin 6) (k : Nat) (d : Int)
    (hprefix : run m k (blankAt q) =
      some (shiftConfig d (blankAt q'))) (n : Nat) :
    HaltsAfterAt m q (k + n) ↔ HaltsAfterAt m q' n := by
  unfold HaltsAfterAt
  have suffix (r : Nat) : run m (k + r) (blankAt q) =
      (run m r (blankAt q')).map (shiftConfig d) := by
    rw [run_append, hprefix]
    simp only [Option.bind_some]
    exact shift_run d m (blankAt q') r
  rw [Nat.add_assoc, suffix n, suffix (n + 1)]
  cases h : run m n (blankAt q') <;>
    cases h' : run m (n + 1) (blankAt q') <;> simp [h, h']

#print axioms blank_prefix_haltsAt_offset

end BB6Coverage
