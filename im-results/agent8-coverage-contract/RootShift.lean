import Symmetry

namespace BB6Coverage

/-- Translate both head and full infinite tape by an integer displacement. -/
def shiftConfig (j : Int) (c : Config) : Config :=
  {state := c.state, head := c.head + j, tape := fun x => c.tape (x-j)}

@[simp] theorem shift_readSlot (j : Int) (c : Config) :
    readSlot (shiftConfig j c) = readSlot c := by
  simp [shiftConfig, readSlot]

theorem shift_applyMove (j : Int) (c : Config) (t : Move) :
    shiftConfig j (applyMove c t) = applyMove (shiftConfig j c) t := by
  cases c with
  | mk s h tape =>
    cases t with
    | mk w r q =>
      simp [shiftConfig, applyMove]
      constructor
      · omega
      · funext x
        have hx : (x - j = h) ↔ (x = h+j) := by omega
        simp [hx]
        rfl

theorem shift_rawStep (j : Int) (m : Machine) (c : Config) :
    rawStep m (shiftConfig j c) = (rawStep m c).map (shiftConfig j) := by
  simp only [rawStep, shift_readSlot]
  cases h : m (readSlot c) with
  | none => simp
  | some t => simp [shift_applyMove]

theorem shift_run (j : Int) (m : Machine) (c : Config) (n : Nat) :
    run m n (shiftConfig j c) = (run m n c).map (shiftConfig j) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run, ih]
    cases h : run m n c with
    | none => simp
    | some d => simp [shift_rawStep]

@[simp] theorem shift_shift (j k : Int) (c : Config) :
    shiftConfig j (shiftConfig k c) = shiftConfig (j+k) c := by
  cases c with
  | mk s h tape =>
    simp [shiftConfig]
    constructor
    · omega
    · funext x
      congr 1
      omega

/-- Concatenation of raw Turing machine run prefixes (including halt). -/
theorem run_append (m : Machine) (c : Config) (a b : Nat) :
    run m (a+b) c = (run m a c).bind (run m b) := by
  induction b with
  | zero => simp [run]
  | succ b ih =>
    calc
      run m (a+(b+1)) c = (run m (a+b) c).bind (rawStep m) := by rw [Nat.add_succ]; rfl
      _ = ((run m a c).bind (run m b)).bind (rawStep m) := by rw [ih]
      _ = (run m a c).bind (run m (b+1)) := by
        cases h : run m a c with
        | none => simp
        | some d => simp [run]

/-- A run that reaches a translated blank A configuration and never stops
from there is guaranteed to remain live afterwards. -/
theorem live_shifted_blank (m : Machine) (j : Int)
    (hne : NeverHalts m) (n : Nat) :
    (run m n (shiftConfig j blank)).isSome = true := by
  rw [shift_run]
  cases h : run m n blank with
  | none =>
      have hh := hne n
      simp [h] at hh
  | some d => rfl


/-- A finite live prefix into a translated original blank start promotes
original-root nonhalting to all-time nonhalting from another state root.
The prefix itself establishes liveness at every earlier time. -/
theorem shifted_blank_root_never (m : Machine) (root : Fin 6)
    (delay : Nat) (j : Int)
    (hprefix : run m delay (blankAt root) = some (shiftConfig j blank))
    (hne : NeverHalts m) :
    ∀ n, (run m n (blankAt root)).isSome = true := by
  intro n
  by_cases hle : n ≤ delay
  · cases hr : run m n (blankAt root) with
    | some c => rfl
    | none =>
        have heq : delay = n + (delay-n) := by omega
        have hrest : run m delay (blankAt root) = none := by
          calc
            run m delay (blankAt root) = run m (n+(delay-n)) (blankAt root) := by rw [← heq]
            _ = (run m n (blankAt root)).bind (run m (delay-n)) := run_append m (blankAt root) n (delay-n)
            _ = none := by rw [hr]; rfl
        simp [hprefix] at hrest
  · have hge : delay ≤ n := by omega
    have heq : n = delay+(n-delay) := by omega
    rw [heq, run_append, hprefix]
    exact live_shifted_blank m j hne (n-delay)

#print axioms shifted_blank_root_never

#print axioms shift_run
#print axioms run_append
#print axioms live_shifted_blank
end BB6Coverage
