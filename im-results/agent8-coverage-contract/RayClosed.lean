import Frontier
namespace BB6Coverage
/-- The current head at n and its entire future right half-tape are blank. -/
def forwardClear (c : Config) (n : Nat) : Prop :=
  c.head = (n : Int) ∧ ∀ x : Int, (n : Int) ≤ x → c.tape x = false

def rightClosed (m : Machine) (S : Fin 6 → Prop) : Prop :=
  ∀ s, S s → ∃ mv : Move,
    m (s, false) = some mv ∧ mv.right = true ∧ S mv.next

theorem forwardClear_move (c : Config) (n : Nat) (mv : Move)
    (hclear : forwardClear c n) (hright : mv.right = true) :
    forwardClear (applyMove c mv) (n+1) := by
  constructor
  · simp only [forwardClear] at hclear
    simp [applyMove, hright, hclear.1]
  · intro x hx
    have hneq : x ≠ c.head := by
      rw [hclear.1]
      omega
    have hge : (n : Int) ≤ x := by omega
    simp [applyMove, hneq, hclear.2 x hge]

theorem rightClosed_run (m : Machine) (S : Fin 6 → Prop)
    (hstart : S (⟨0, by decide⟩ : Fin 6))
    (hclose : rightClosed m S) (n : Nat) :
    ∃ c, run m n blank = some c ∧ S c.state ∧ forwardClear c n := by
  induction n with
  | zero =>
    refine ⟨blank, rfl, hstart, ?_⟩
    simp [forwardClear, blank]
  | succ n ih =>
    obtain ⟨c, hc, hs, hclear⟩ := ih
    obtain ⟨mv, hm, hr, hnext⟩ := hclose c.state hs
    have hread : readSlot c = (c.state, false) := by
      have hzero : c.tape c.head = false := by
        apply hclear.2
        rw [hclear.1]
        omega
      exact Prod.ext rfl hzero
    have hstep : rawStep m c = some (applyMove c mv) := by
      simp only [rawStep, hread, hm, Option.map_some]
    refine ⟨applyMove c mv, ?_, hnext, forwardClear_move c n mv hclear hr⟩
    simpa only [run, hc, Option.bind_some] using hstep

theorem rightClosed_never (m : Machine) (S : Fin 6 → Prop)
    (hstart : S (⟨0, by decide⟩ : Fin 6))
    (hclose : rightClosed m S) : NeverHalts m := by
  intro n
  obtain ⟨c, hc, _, _⟩ := rightClosed_run m S hstart hclose n
  simp [hc]

/-- Pristine mirror-image left ray, allowing arbitrary symbols behind. -/
def backwardClear (c : Config) (n : Nat) : Prop :=
  c.head = -(n : Int) ∧ ∀ x : Int, x ≤ -(n : Int) → c.tape x = false

def leftClosed (m : Machine) (S : Fin 6 → Prop) : Prop :=
  ∀ s, S s → ∃ mv : Move,
    m (s, false) = some mv ∧ mv.right = false ∧ S mv.next

theorem backwardClear_move (c : Config) (n : Nat) (mv : Move)
    (hclear : backwardClear c n) (hleft : mv.right = false) :
    backwardClear (applyMove c mv) (n+1) := by
  constructor
  · simp only [backwardClear] at hclear
    simp [applyMove, hleft, hclear.1]
    omega
  · intro x hx
    have hneq : x ≠ c.head := by
      rw [hclear.1]
      omega
    have hle : x ≤ -(n : Int) := by omega
    simp [applyMove, hneq, hclear.2 x hle]

theorem leftClosed_run (m : Machine) (S : Fin 6 → Prop)
    (hstart : S (⟨0, by decide⟩ : Fin 6))
    (hclose : leftClosed m S) (n : Nat) :
    ∃ c, run m n blank = some c ∧ S c.state ∧ backwardClear c n := by
  induction n with
  | zero =>
    refine ⟨blank, rfl, hstart, ?_⟩
    simp [backwardClear, blank]
  | succ n ih =>
    obtain ⟨c, hc, hs, hclear⟩ := ih
    obtain ⟨mv, hm, hr, hnext⟩ := hclose c.state hs
    have hread : readSlot c = (c.state, false) := by
      have hzero : c.tape c.head = false := by
        apply hclear.2
        rw [hclear.1]
        omega
      exact Prod.ext rfl hzero
    have hstep : rawStep m c = some (applyMove c mv) := by
      simp only [rawStep, hread, hm, Option.map_some]
    refine ⟨applyMove c mv, ?_, hnext, backwardClear_move c n mv hclear hr⟩
    simpa only [run, hc, Option.bind_some] using hstep

theorem leftClosed_never (m : Machine) (S : Fin 6 → Prop)
    (hstart : S (⟨0, by decide⟩ : Fin 6))
    (hclose : leftClosed m S) : NeverHalts m := by
  intro n
  obtain ⟨c, hc, _, _⟩ := leftClosed_run m S hstart hclose n
  simp [hc]

/-- An all-time leftward nonhalting certificate over a partial table. -/
theorem leftClosed_leaf (p : PartialMachine) (S : Fin 6 → Prop)
    (hstart : S (⟨0, by decide⟩ : Fin 6))
    (hclose : ∀ s, S s → ∃ mv : Move,
      p (s, false) = some (some mv) ∧ mv.right = false ∧ S mv.next)
    (bound : Nat) : Cover (DecidedBelow bound) p := by
  apply Cover.leaf
  intro m hm
  left
  apply leftClosed_never m S hstart
  intro s hs
  obtain ⟨mv, hp, hr, hn⟩ := hclose s hs
  exact ⟨mv, hm (s, false) (some mv) hp, hr, hn⟩

/-- An all-time rightward nonhalting certificate over a partial table. -/
theorem rightClosed_leaf (p : PartialMachine) (S : Fin 6 → Prop)
    (hstart : S (⟨0, by decide⟩ : Fin 6))
    (hclose : ∀ s, S s → ∃ mv : Move,
      p (s, false) = some (some mv) ∧ mv.right = true ∧ S mv.next)
    (bound : Nat) : Cover (DecidedBelow bound) p := by
  apply Cover.leaf
  intro m hm
  left
  apply rightClosed_never m S hstart
  intro s hs
  obtain ⟨mv, hp, hr, hn⟩ := hclose s hs
  exact ⟨mv, hm (s, false) (some mv) hp, hr, hn⟩

/-- Two-state right-sweeping cycle depositing ones every other cell. -/
def twoRayState (s : Fin 6) : Prop :=
  s = ⟨0, by decide⟩ ∨ s = ⟨1, by decide⟩

def twoRayTable : PartialMachine := fun s =>
  if s = (⟨0, by decide⟩, false) then
    some (some ⟨true, true, ⟨1, by decide⟩⟩)
  else if s = (⟨1, by decide⟩, false) then
    some (some ⟨false, true, ⟨0, by decide⟩⟩)
  else none

/-- The 25^10 total completions of the remaining slots all diverge. -/
theorem twoRay_certificate (bound : Nat) :
    Cover (DecidedBelow bound) twoRayTable := by
  apply rightClosed_leaf twoRayTable twoRayState (Or.inl rfl)
  · intro s hs
    rcases hs with h | h
    · subst s
      exact ⟨⟨true, true, ⟨1, by decide⟩⟩, by decide, rfl, Or.inr rfl⟩
    · subst s
      exact ⟨⟨false, true, ⟨0, by decide⟩⟩, by decide, rfl, Or.inl rfl⟩

#print axioms rightClosed_run
#print axioms leftClosed_run
#print axioms rightClosed_never
#print axioms leftClosed_never
#print axioms rightClosed_leaf
#print axioms leftClosed_leaf
#print axioms twoRay_certificate
end BB6Coverage
