import WeightedSymmetry

namespace BB6.Agent25EqualEntrySymmetry
open BB6Coverage BB6.Agent16WeightedSymmetry

/-- Once the first physical configurations coincide, every positive-time
    configuration coincides, even if the distinguished initial states differ. -/
theorem run_succ_eq_of_rawStep (m : Machine) (c d : Config)
    (h : rawStep m c = rawStep m d) (n : Nat) :
    run m (n+1) c = run m (n+1) d := by
  induction n with
  | zero => simpa [run] using h
  | succ n ih =>
    change (run m (n+1) c).bind (rawStep m) = (run m (n+1) d).bind (rawStep m)
    rw [ih]

/-- For a blank tape, identical outgoing instructions erase the distinction
    between the start labels after one step. -/
theorem equal_blank_entry (m : Machine) (q : Fin 6)
    (h : m (0,false) = m (q,false)) :
    rawStep m blank = rawStep m (blankAt q) := by
  change (m (0,false)).map (applyMove blank) =
    (m (q,false)).map (applyMove (blankAt q))
  rw [h]
  cases m (q,false) <;> rfl

/-- A non-root-fixing renaming is sound for blank-start nonhalting when the
    two start labels in the renamed machine have identical blank transitions. -/
theorem never_of_rename_equal_entry (e : StatePerm) (m : Machine)
    (hentry : renameTable e m (0,false) = renameTable e m (e.forward 0,false))
    (h : NeverHalts (renameTable e m)) : NeverHalts m := by
  intro n
  cases n with
  | zero => rfl
  | succ n =>
    have he := run_succ_eq_of_rawStep (renameTable e m) blank (blankAt (e.forward 0))
      (equal_blank_entry (renameTable e m) (e.forward 0) hentry) n
    have hr : run (renameTable e m) (n+1) (blankAt (e.forward 0)) =
        (run m (n+1) blank).map (renameConfig e) := by
      exact rename_run e m blank (n+1)
    have hn := h (n+1)
    rw [he,hr] at hn
    cases hh : run m (n+1) blank with
    | none => simp [hh] at hn
    | some d => rfl

/-- The same criterion lifts a complete partial-machine nonhalting certificate;
    both equal-entry instructions must be assigned, not mere unknown slots. -/
theorem never_transport_equal_entry (e : StatePerm) {p q : PartialMachine}
    (hpq : renamePartial e p = q) (t : Transition)
    (h0 : q (0,false) = some t) (h1 : q (e.forward 0,false) = some t)
    (hq : ∀ m, compatible q m → NeverHalts m) :
    ∀ m, compatible p m → NeverHalts m := by
  intro m hm
  have hc := rename_compatible e hm
  rw [hpq] at hc
  apply never_of_rename_equal_entry e m _ (hq _ hc)
  exact (hc _ t h0).trans (hc _ t h1).symm

#print axioms run_succ_eq_of_rawStep
#print axioms never_of_rename_equal_entry
#print axioms never_transport_equal_entry
end BB6.Agent25EqualEntrySymmetry
