import Frontier

namespace BB6Coverage

/-- The reflection acts on the bi-infinite tape by x ↦ -x. -/
def mirrorConfig (c : Config) : Config :=
  { state := c.state, head := -c.head, tape := fun x => c.tape (-x) }

def reflectMove (t : Move) : Move :=
  { t with right := !t.right }

def reflectTable (m : Machine) : Machine := fun s =>
  (m s).map reflectMove

@[simp] theorem mirror_readSlot (c : Config) :
    readSlot (mirrorConfig c) = readSlot c := by
  simp [readSlot, mirrorConfig]

@[simp] theorem mirror_involution (c : Config) :
    mirrorConfig (mirrorConfig c) = c := by
  cases c with
  | mk state head tape =>
    simp [mirrorConfig]

@[simp] theorem reflectMove_involution (t : Move) :
    reflectMove (reflectMove t) = t := by
  cases t
  simp [reflectMove]

@[simp] theorem reflectTable_involution (m : Machine) :
    reflectTable (reflectTable m) = m := by
  funext s
  cases h : m s with
  | none => simp [reflectTable, h]
  | some t => simp [reflectTable, h, reflectMove_involution]

/-- Reflection commutes exactly with each ordinary Turing-machine move. -/
theorem mirror_applyMove (c : Config) (t : Move) :
    mirrorConfig (applyMove c t) =
      applyMove (mirrorConfig c) (reflectMove t) := by
  cases c with
  | mk state head tape =>
    cases t with
    | mk w r q =>
      cases r <;>
        simp [mirrorConfig, applyMove, reflectMove] <;>
        (constructor
         · omega
         · funext x
           have hx : (-x = head) ↔ x = -head := by omega
           simp [hx])

/-- Reflection respects a single transition, including an undefined halt. -/
theorem mirror_rawStep (m : Machine) (c : Config) :
    (rawStep (reflectTable m) (mirrorConfig c)) =
      (rawStep m c).map mirrorConfig := by
  simp only [rawStep, mirror_readSlot, reflectTable]
  cases h : m (readSlot c) with
  | none => simp
  | some t => simp [mirror_applyMove]

/-- Every finite prefix of the reflected machine is the geometric reflection
    of the original prefix with the same number of steps. -/
theorem mirror_run (m : Machine) (c : Config) (n : Nat) :
    run (reflectTable m) n (mirrorConfig c) =
      (run m n c).map mirrorConfig := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run, ih]
    cases h : run m n c with
    | none => simp
    | some d => simp [mirror_rawStep]

@[simp] theorem mirror_blank : mirrorConfig blank = blank := by
  simp [mirrorConfig, blank]

/-- Blank tape halting times are invariant under left/right reflection. -/
theorem reflect_halts_iff (m : Machine) (n : Nat) :
    HaltsAfter (reflectTable m) n ↔ HaltsAfter m n := by
  have hn : run (reflectTable m) n blank = (run m n blank).map mirrorConfig := by
    simpa only [mirror_blank] using mirror_run m blank n
  have hs : run (reflectTable m) (n+1) blank =
      (run m (n+1) blank).map mirrorConfig := by
    simpa only [mirror_blank] using mirror_run m blank (n+1)
  unfold HaltsAfter
  rw [hn, hs]
  cases h : run m n blank <;> cases h2 : run m (n+1) blank <;> simp

/-- An arbitrary state-permutation transports a machine and its start state
    together. This covers the full 6! label-normalization group. -/
structure StatePerm where
  forward : Fin 6 → Fin 6
  backward : Fin 6 → Fin 6
  leftInverse : ∀ s, backward (forward s) = s
  rightInverse : ∀ s, forward (backward s) = s

def renameConfig (e : StatePerm) (c : Config) : Config :=
  { c with state := e.forward c.state }

def renameMove (e : StatePerm) (t : Move) : Move :=
  { t with next := e.forward t.next }

def renameTable (e : StatePerm) (m : Machine) : Machine := fun s =>
  (m (e.backward s.1, s.2)).map (renameMove e)

@[simp] theorem rename_readSlot (e : StatePerm) (c : Config) :
    readSlot (renameConfig e c) = (e.forward c.state, c.tape c.head) := rfl

@[simp] theorem rename_applyMove (e : StatePerm) (c : Config) (t : Move) :
    renameConfig e (applyMove c t) =
      applyMove (renameConfig e c) (renameMove e t) := by
  rfl

theorem rename_rawStep (e : StatePerm) (m : Machine) (c : Config) :
    rawStep (renameTable e m) (renameConfig e c) =
      (rawStep m c).map (renameConfig e) := by
  have hlook : renameTable e m (readSlot (renameConfig e c)) =
      (m (readSlot c)).map (renameMove e) := by
    simp [renameTable, readSlot, renameConfig, e.leftInverse]
  simp only [rawStep, hlook]
  cases h : m (readSlot c) with
  | none => simp
  | some t => simp [rename_applyMove]

theorem rename_run (e : StatePerm) (m : Machine) (c : Config) (n : Nat) :
    run (renameTable e m) n (renameConfig e c) =
      (run m n c).map (renameConfig e) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run, ih]
    cases h : run m n c with
    | none => simp
    | some d => simp [rename_rawStep]

/-- Arbitrary blank state, needed to prevent unsound root collapsing when
    different catalogued machines share one unrooted transition table. -/
def blankAt (s : Fin 6) : Config :=
  { state := s, head := 0, tape := fun _ => false }

def HaltsAfterAt (m : Machine) (s : Fin 6) (n : Nat) : Prop :=
  (run m n (blankAt s)).isSome = true ∧ run m (n+1) (blankAt s) = none

@[simp] theorem rename_blankAt (e : StatePerm) (s : Fin 6) :
    renameConfig e (blankAt s) = blankAt (e.forward s) := rfl

@[simp] theorem blankAt_zero : blankAt ⟨0, by decide⟩ = blank := rfl

theorem rename_haltsAt_iff (e : StatePerm) (m : Machine)
    (s : Fin 6) (n : Nat) :
    HaltsAfterAt (renameTable e m) (e.forward s) n ↔ HaltsAfterAt m s n := by
  have hn : run (renameTable e m) n (blankAt (e.forward s)) =
      (run m n (blankAt s)).map (renameConfig e) := by
    simpa only [rename_blankAt] using rename_run e m (blankAt s) n
  have hs : run (renameTable e m) (n+1) (blankAt (e.forward s)) =
      (run m (n+1) (blankAt s)).map (renameConfig e) := by
    simpa only [rename_blankAt] using rename_run e m (blankAt s) (n+1)
  unfold HaltsAfterAt
  rw [hn, hs]
  cases h : run m n (blankAt s) <;>
    cases h2 : run m (n+1) (blankAt s) <;> simp

/-- Explicit normalization warning: if an arbitrary state permutation sends
    the distinguished A state to another state, the equivalent original-root
    computation starts in that other state, not automatically in A. -/
theorem relabeled_A_haltsAt (e : StatePerm) (m : Machine) (n : Nat) :
    HaltsAfterAt (renameTable e m) (e.forward ⟨0, by decide⟩) n ↔ HaltsAfter m n := by
  simpa only [HaltsAfterAt, HaltsAfter, blankAt_zero] using
    rename_haltsAt_iff e m ⟨0, by decide⟩ n

/-- Mirror symmetry preserves halting time for any blank start state. -/
@[simp] theorem mirror_blankAt (s : Fin 6) :
    mirrorConfig (blankAt s) = blankAt s := by
  simp [mirrorConfig, blankAt]

theorem mirror_haltsAt_iff (m : Machine) (s : Fin 6) (n : Nat) :
    HaltsAfterAt (reflectTable m) s n ↔ HaltsAfterAt m s n := by
  have hn : run (reflectTable m) n (blankAt s) =
      (run m n (blankAt s)).map mirrorConfig := by
    simpa only [mirror_blankAt] using mirror_run m (blankAt s) n
  have hs : run (reflectTable m) (n+1) (blankAt s) =
      (run m (n+1) (blankAt s)).map mirrorConfig := by
    simpa only [mirror_blankAt] using mirror_run m (blankAt s) (n+1)
  unfold HaltsAfterAt
  rw [hn, hs]
  cases h : run m n (blankAt s) <;> cases h2 : run m (n+1) (blankAt s) <;> simp

/-- All 720 state renamings and the optional L/R reflection are safe
    for fixed-root halting-time classification if the root moves with its
    state label. -/
def normalizedTable (e : StatePerm) (mirror : Bool) (m : Machine) : Machine :=
  renameTable e (if mirror then reflectTable m else m)

theorem normalized_haltsAt_iff (e : StatePerm) (mirror : Bool)
    (m : Machine) (s : Fin 6) (n : Nat) :
    HaltsAfterAt (normalizedTable e mirror m) (e.forward s) n ↔
      HaltsAfterAt m s n := by
  cases mirror with
  | false =>
    change HaltsAfterAt (renameTable e m) (e.forward s) n ↔ HaltsAfterAt m s n
    exact rename_haltsAt_iff e m s n
  | true =>
    change HaltsAfterAt (renameTable e (reflectTable m)) (e.forward s) n ↔
      HaltsAfterAt m s n
    exact (rename_haltsAt_iff e (reflectTable m) s n).trans
      (mirror_haltsAt_iff m s n)

#print axioms mirror_haltsAt_iff
#print axioms normalized_haltsAt_iff

#print axioms rename_rawStep
#print axioms rename_run
#print axioms rename_haltsAt_iff
#print axioms relabeled_A_haltsAt

#print axioms mirror_applyMove
#print axioms mirror_rawStep
#print axioms mirror_run
#print axioms reflect_halts_iff
end BB6Coverage
