import Frontier
namespace BB6Coverage

/-- A cell is in the unexplored ray in the chosen direction. -/
def Ahead (dir : Bool) (h x : Int) : Prop :=
  if dir then h ≤ x else x ≤ h

/-- A set of working states is forward closed along transitions that always
    move in the same direction while reading a previously untouched zero. -/
def DriftClosed (m : Machine) (states : Fin 6 → Prop) (dir : Bool) : Prop :=
  ∀ s, states s → ∃ w next,
    m (s, false) = some ⟨w, dir, next⟩ ∧ states next

theorem step_in_blank_ray (m : Machine) (states : Fin 6 → Prop)
    (dir : Bool) (hclosed : DriftClosed m states dir)
    (c : Config) (hs : states c.state)
    (hblank : ∀ x, Ahead dir c.head x → c.tape x = false) :
    ∃ d, rawStep m c = some d ∧ states d.state ∧
      ∀ x, Ahead dir d.head x → d.tape x = false := by
  obtain ⟨w, next, hm, hn⟩ := hclosed c.state hs
  let d : Config := applyMove c ⟨w, dir, next⟩
  refine ⟨d, ?_, hn, ?_⟩
  · have hz : c.tape c.head = false := hblank c.head (by cases dir <;> simp [Ahead])
    simp [rawStep, readSlot, hz, hm, d]
  · intro x hx
    have hne : x ≠ c.head := by
      cases dir <;> simp [Ahead, d, applyMove] at hx <;> omega
    have ha : Ahead dir c.head x := by
      cases dir <;> simp [Ahead, d, applyMove] at hx ⊢ <;> omega
    simp [d, applyMove, hne, hblank x ha]

/-- Every prefix exists while the control stays inside the finite state set
    and the entire unvisited half-tape stays blank. -/
theorem drift_run_invariant (m : Machine) (states : Fin 6 → Prop)
    (dir : Bool) (hinit : states (⟨0, by decide⟩ : Fin 6))
    (hclosed : DriftClosed m states dir) (n : Nat) :
    ∃ c, run m n blank = some c ∧ states c.state ∧
      ∀ x, Ahead dir c.head x → c.tape x = false := by
  induction n with
  | zero =>
      refine ⟨blank, rfl, hinit, ?_⟩
      intro x hx
      rfl
  | succ n ih =>
      obtain ⟨c, hc, hs, hb⟩ := ih
      obtain ⟨d, hd, hsd, hbd⟩ :=
        step_in_blank_ray m states dir hclosed c hs hb
      exact ⟨d, by simp [run, hc, hd], hsd, hbd⟩

/-- A finite closed control graph on fresh zero cells certifies the entire
    blank-origin run, irrespective of all other machine-table entries. -/
theorem directed_drift_never (m : Machine) (states : Fin 6 → Prop)
    (dir : Bool) (hinit : states (⟨0, by decide⟩ : Fin 6))
    (hclosed : DriftClosed m states dir) : NeverHalts m := by
  intro n
  obtain ⟨c, hc, _, _⟩ := drift_run_invariant m states dir hinit hclosed n
  simp [hc]

/-- A sparse table explicitly contains the finite closure witnesses.
    Every unconstrained slot may be completed arbitrarily. -/
def PartialDriftClosed (p : PartialMachine) (states : Fin 6 → Prop)
    (dir : Bool) : Prop :=
  ∀ s, states s → ∃ w next,
    p (s, false) = some (some ⟨w, dir, next⟩) ∧ states next

theorem partial_drift_cover (p : PartialMachine)
    (states : Fin 6 → Prop) (dir : Bool) (B : Nat)
    (hinit : states (⟨0, by decide⟩ : Fin 6))
    (hclosed : PartialDriftClosed p states dir) :
    Cover (DecidedBelow B) p := by
  apply Cover.leaf
  intro m hm
  left
  apply directed_drift_never m states dir hinit
  intro s hs
  obtain ⟨w, next, hw, hn⟩ := hclosed s hs
  exact ⟨w, next, hm (s, false) (some ⟨w, dir, next⟩) hw, hn⟩

/-- The two-state alternating right drift: A/0 writes 1 and enters B;
    B/0 writes 0 and returns to A. All other ten slots are unrestricted. -/
def alternatingStates (s : Fin 6) : Prop :=
  s = 0 ∨ s = 1

def alternatingTable : PartialMachine := fun slot =>
  if slot = (0, false) then some (some ⟨true, true, 1⟩)
  else if slot = (1, false) then some (some ⟨false, true, 0⟩)
  else none

private theorem alternating_closed :
    PartialDriftClosed alternatingTable alternatingStates true := by
  intro s hs
  rcases hs with hs | hs
  · subst s
    exact ⟨true, 1, by decide, Or.inr rfl⟩
  · subst s
    exact ⟨false, 0, by decide, Or.inl rfl⟩

/-- A genuine sparse nonhalting coverage leaf covering all 25^10 table
    completions, even with arbitrary 1-read behavior on A and B. -/
theorem alternating_cover (B : Nat) :
    Cover (DecidedBelow B) alternatingTable := by
  exact partial_drift_cover alternatingTable alternatingStates true B
    (Or.inl rfl) alternating_closed


/-- A finite state-set is closed under zero-writing transitions on blank. Its
    instructions may change direction at every step. -/
def ZeroWriterClosed (m : Machine) (states : Fin 6 → Prop) : Prop :=
  ∀ s, states s → ∃ dir next,
    m (s, false) = some ⟨false, dir, next⟩ ∧ states next

private theorem zero_writer_step (m : Machine) (states : Fin 6 → Prop)
    (hclosed : ZeroWriterClosed m states)
    (c : Config) (hs : states c.state)
    (hblank : ∀ x, c.tape x = false) :
    ∃ d, rawStep m c = some d ∧ states d.state ∧
      ∀ x, d.tape x = false := by
  obtain ⟨dir, next, hm, hn⟩ := hclosed c.state hs
  let d : Config := applyMove c ⟨false, dir, next⟩
  refine ⟨d, ?_, hn, ?_⟩
  · have hz : c.tape c.head = false := hblank c.head
    simp [rawStep, readSlot, hz, hm, d]
  · intro x
    simp [d, applyMove, hblank x]

/-- Exact all-time blank-tape invariant and nonhalting for any finite-control
    zero-writer, irrespective of direction changes. -/
theorem zero_writer_never (m : Machine) (states : Fin 6 → Prop)
    (hinit : states (⟨0, by decide⟩ : Fin 6))
    (hclosed : ZeroWriterClosed m states) : NeverHalts m := by
  have all_time : ∀ n, ∃ c, run m n blank = some c ∧
      states c.state ∧ ∀ x, c.tape x = false := by
    intro n
    induction n with
    | zero =>
        exact ⟨blank, rfl, hinit, by intro x; rfl⟩
    | succ n ih =>
        obtain ⟨c, hc, hs, hb⟩ := ih
        obtain ⟨d, hd, hsd, hbd⟩ := zero_writer_step m states hclosed c hs hb
        exact ⟨d, by simp [run, hc, hd], hsd, hbd⟩
  intro n
  obtain ⟨c, hc, _, _⟩ := all_time n
  simp [hc]

def PartialZeroWriterClosed (p : PartialMachine) (states : Fin 6 → Prop) : Prop :=
  ∀ s, states s → ∃ dir next,
    p (s, false) = some (some ⟨false, dir, next⟩) ∧ states next

/-- A genuine sparse nonhalting certificate for closed zero-writer controls
    with arbitrary per-state head directions. -/
theorem partial_zero_writer_cover (p : PartialMachine)
    (states : Fin 6 → Prop) (B : Nat)
    (hinit : states (⟨0, by decide⟩ : Fin 6))
    (hclosed : PartialZeroWriterClosed p states) :
    Cover (DecidedBelow B) p := by
  apply Cover.leaf
  intro m hm
  left
  apply zero_writer_never m states hinit
  intro s hs
  obtain ⟨dir, next, h, hn⟩ := hclosed s hs
  exact ⟨dir, next, hm (s, false) (some ⟨false, dir, next⟩) h, hn⟩

/-- An alternating left/right blank-tape cycle, with all other ten table
    entries arbitrary, is a certified zero-writer leaf. -/
def alternatingZeroTable : PartialMachine := fun slot =>
  if slot = (0, false) then some (some ⟨false, true, 1⟩)
  else if slot = (1, false) then some (some ⟨false, false, 0⟩)
  else none

private theorem alternating_zero_closed :
    PartialZeroWriterClosed alternatingZeroTable alternatingStates := by
  intro s hs
  rcases hs with hs | hs
  · subst s
    exact ⟨true, 1, by decide, Or.inr rfl⟩
  · subst s
    exact ⟨false, 0, by decide, Or.inl rfl⟩

theorem alternating_zero_cover (B : Nat) :
    Cover (DecidedBelow B) alternatingZeroTable := by
  exact partial_zero_writer_cover alternatingZeroTable alternatingStates B
    (Or.inl rfl) alternating_zero_closed

#print axioms zero_writer_never
#print axioms partial_zero_writer_cover
#print axioms alternating_zero_cover

#print axioms alternating_cover
#print axioms directed_drift_never
#print axioms partial_drift_cover
end BB6Coverage
