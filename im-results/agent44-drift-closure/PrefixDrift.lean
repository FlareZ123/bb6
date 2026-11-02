import DirectedDrift

namespace BB6Coverage

/-- A closed drift region may be entered after arbitrary finite preprocessing.
    The tape behind the head is allowed to contain arbitrary data. -/
theorem directed_drift_from (m : Machine) (states : Fin 6 → Prop)
    (dir : Bool) (c : Config)
    (hstate : states c.state)
    (hblank : ∀ x, Ahead dir c.head x → c.tape x = false)
    (hclosed : DriftClosed m states dir) (n : Nat) :
    ∃ d, run m n c = some d ∧ states d.state ∧
      ∀ x, Ahead dir d.head x → d.tape x = false := by
  induction n with
  | zero => exact ⟨c, rfl, hstate, hblank⟩
  | succ n ih =>
      obtain ⟨d, hd, hs, hb⟩ := ih
      obtain ⟨e, he, hse, hbe⟩ :=
        step_in_blank_ray m states dir hclosed d hs hb
      exact ⟨e, by simp [run, hd, he], hse, hbe⟩

private theorem drift_run_add (m : Machine) (c : Config) (n k : Nat) :
    run m (n+k) c = (run m n c).bind (run m k) := by
  induction k with
  | zero => simp [run]
  | succ k ih =>
      rw [Nat.add_succ, run, ih]
      cases h : run m n c with
      | none => simp
      | some d => rfl

/-- Reaching a forward-closed blank ray after any genuine finite prefix
    proves that the original blank run never halted and never will halt. -/
theorem prefix_drift_never (m : Machine) (states : Fin 6 → Prop)
    (dir : Bool) (k : Nat) (c : Config)
    (hentry : run m k blank = some c)
    (hstate : states c.state)
    (hblank : ∀ x, Ahead dir c.head x → c.tape x = false)
    (hclosed : DriftClosed m states dir) : NeverHalts m := by
  intro n
  by_cases hle : n ≤ k
  · cases hn : run m n blank with
    | none =>
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
        have hnone : run m k blank = none := by
          rw [hd, drift_run_add, hn]
          rfl
        rw [hnone] at hentry
        contradiction
    | some d => rfl
  · have hge : k ≤ n := by omega
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hge
    obtain ⟨e, he, _, _⟩ :=
      directed_drift_from m states dir c hstate hblank hclosed d
    rw [hd, drift_run_add, hentry]
    simp [he]

/-- A sparse certificate may enter a directed drift after an exact finite
    prefix, provided every transition consulted during that prefix was assigned. -/
theorem prefix_drift_cover (p : PartialMachine) (w : Machine)
    (states : Fin 6 → Prop) (dir : Bool) (k : Nat) (c : Config) (B : Nat)
    (hw : compatible p w)
    (hknown : ∀ i, i < k → ∀ d, run w i blank = some d →
      p (readSlot d) = some (w (readSlot d)))
    (hentry : run w k blank = some c)
    (hstate : states c.state)
    (hblank : ∀ x, Ahead dir c.head x → c.tape x = false)
    (hclosed : PartialDriftClosed p states dir) :
    Cover (DecidedBelow B) p := by
  apply Cover.leaf
  intro m hm
  left
  have he : run m k blank = some c := by
    rw [← common_prefix_of_partial_table p w m blank k hw hm hknown]
    exact hentry
  apply prefix_drift_never m states dir k c he hstate hblank
  intro state hs
  obtain ⟨write, next, h, hn⟩ := hclosed state hs
  exact ⟨write, next, hm (state, false) (some ⟨write, dir, next⟩) h, hn⟩

#print axioms directed_drift_from
#print axioms prefix_drift_never
#print axioms prefix_drift_cover

end BB6Coverage
