import Std

namespace BB6Coverage

abbrev Slot := Fin 6 × Bool
structure Move where
  write : Bool
  right : Bool
  next : Fin 6
  deriving DecidableEq, Repr

abbrev Transition := Option Move
abbrev Machine := Slot → Transition
abbrev PartialMachine := Slot → Option Transition

def compatible (p : PartialMachine) (m : Machine) : Prop :=
  ∀ slot t, p slot = some t → m slot = t

def refine (p : PartialMachine) (slot : Slot) (t : Transition) : PartialMachine :=
  fun other => if other = slot then some t else p other

theorem compatible_refine (p : PartialMachine) (m : Machine) (s : Slot)
    (h : compatible p m) :
    compatible (refine p s (m s)) m := by
  intro other t ht
  by_cases heq : other = s
  · subst other
    simpa [refine] using ht
  · have hold : p other = some t := by simpa [refine, heq] using ht
    exact h other t hold

theorem compatible_refine_iff (p : PartialMachine) (m : Machine) (s : Slot)
    (hs : p s = none) (t : Transition) :
    compatible (refine p s t) m ↔ compatible p m ∧ m s = t := by
  constructor
  · intro h
    constructor
    · intro other v ho
      by_cases heq : other = s
      · subst other
        simp [hs] at ho
      · exact h other v (by simpa [refine, heq] using ho)
    · exact h s t (by simp [refine])
  · intro ⟨h, hst⟩
    simpa [hst] using compatible_refine p m s h

end BB6Coverage

namespace BB6Coverage

structure Config where
  state : Fin 6
  head : Int
  tape : Int → Bool

abbrev readSlot (c : Config) : Slot := (c.state, c.tape c.head)

def applyMove (c : Config) (t : Move) : Config :=
  { state := t.next
    head := c.head + (if t.right then 1 else -1)
    tape := fun x => if x = c.head then t.write else c.tape x }

def rawStep (m : Machine) (c : Config) : Option Config :=
  (m (readSlot c)).map (applyMove c)

def run (m : Machine) : Nat → Config → Option Config
  | 0, c => some c
  | n+1, c => (run m n c).bind (rawStep m)

theorem rawStep_agrees (m m' : Machine) (c : Config)
    (heq : m (readSlot c) = m' (readSlot c)) :
    rawStep m c = rawStep m' c := by
  simp [rawStep, heq]

theorem run_agrees_on_prefix (m m' : Machine) (c : Config) (n : Nat)
    (h : ∀ k, k < n → ∀ d, run m k c = some d →
      m (readSlot d) = m' (readSlot d)) :
    run m n c = run m' n c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprefix : ∀ k, k < n → ∀ d, run m k c = some d →
        m (readSlot d) = m' (readSlot d) := by
      intro k hk d hd
      exact h k (Nat.lt_trans hk (Nat.lt_succ_self n)) d hd
    have hprev := ih hprefix
    unfold run
    cases hstate : run m n c with
    | none => simp [hstate, ← hprev]
    | some d =>
      have hstep : rawStep m d = rawStep m' d :=
        rawStep_agrees m m' d (h n (Nat.lt_succ_self n) d hstate)
      simp [hstate, ← hprev, hstep]

/-- If the partial table already fixes every transition consulted in the
    first `n` iterations, *every* compatible total machine executes the same
    raw trace over those `n` steps. -/
theorem common_prefix_of_partial_table (p : PartialMachine)
    (m m' : Machine) (c : Config) (n : Nat)
    (_hm : compatible p m) (hm' : compatible p m')
    (h : ∀ k, k < n → ∀ d, run m k c = some d →
      p (readSlot d) = some (m (readSlot d))) :
    run m n c = run m' n c := by
  apply run_agrees_on_prefix m m' c n
  intro k hk d hd
  exact (hm' _ _ (h k hk d hd)).symm

#print axioms compatible_refine_iff
#print axioms run_agrees_on_prefix
#print axioms common_prefix_of_partial_table

end BB6Coverage

namespace BB6Coverage

/-- 25 one-slot outcomes: 24 ordinary writes, directions, and next states,
    plus the genuine halting outcome. Never conflate this with an *unassigned*
    entry of a sparse table (`none` in `PartialMachine`). -/
def choices : List Transition :=
  none :: (List.finRange 6).flatMap (fun q =>
    [some ⟨false, false, q⟩, some ⟨false, true, q⟩,
     some ⟨true, false, q⟩, some ⟨true, true, q⟩])

theorem choices_complete (t : Transition) : t ∈ choices := by
  cases t with
  | none => simp [choices]
  | some mv =>
    rcases mv with ⟨w, r, q⟩
    have hmem : (some ⟨w, r, q⟩ : Transition) ∈
        (List.finRange 6).flatMap (fun q =>
          [some ⟨false, false, q⟩, some ⟨false, true, q⟩,
           some ⟨true, false, q⟩, some ⟨true, true, q⟩]) := by
      apply List.mem_flatMap.mpr
      refine ⟨q, List.mem_finRange q, ?_⟩
      cases w <;> cases r <;> simp
    simp [choices, hmem]

theorem choices_length : choices.length = 25 := by decide

/-- The exact coverage edge of sparse transition branching. Every total
    completion compatible with a sparse parent belongs to one of the 25
    children obtained by fixing one previously unassigned entry. -/
theorem child_cover (p : PartialMachine) (m : Machine) (slot : Slot)
    (h : compatible p m) (_hu : p slot = none) :
    ∃ t, t ∈ choices ∧ compatible (refine p slot t) m := by
  refine ⟨m slot, choices_complete (m slot), ?_⟩
  exact compatible_refine p m slot h

/-- Each child's compatibility is equivalent to selecting the *actual*
    total transition there, so children with distinct outcomes are disjoint. -/
theorem child_exact (p : PartialMachine) (m : Machine) (slot : Slot)
    (hu : p slot = none) (t : Transition) :
    compatible (refine p slot t) m ↔ compatible p m ∧ m slot = t :=
  compatible_refine_iff p m slot hu t

/-- A sampled finite trace that uses no unassigned transitions is valid for
    every extension and cannot distinguish any two completions. -/
theorem bounded_observation_uniform (p : PartialMachine)
    (m m' : Machine) (c : Config) (n : Nat)
    (h1 : compatible p m) (h2 : compatible p m')
    (known : ∀ k, k < n → ∀ d, run m k c = some d →
       p (readSlot d) = some (m (readSlot d))) :
    run m n c = run m' n c :=
  common_prefix_of_partial_table p m m' c n h1 h2 known

#print axioms choices_complete
#print axioms choices_length
#print axioms child_cover
#print axioms child_exact
#print axioms bounded_observation_uniform

end BB6Coverage

namespace BB6Coverage

/-- At the first unassigned entry of a sparse search node, the total
    machine has a unique 25-way child; all the executions strictly before
    the branching event are also valid for every completion. This is the
    precise local safety property required by sparse enumeration. -/
theorem first_hole_branch (p : PartialMachine) (m : Machine) (c d : Config)
    (n : Nat) (hcompatible : compatible p m)
    (hprefix : ∀ k, k < n → ∀ x, run m k c = some x →
      p (readSlot x) = some (m (readSlot x)))
    (hseen : run m n c = some d)
    (hhole : p (readSlot d) = none) :
    ∃ t, t ∈ choices ∧ compatible (refine p (readSlot d) t) m ∧
      (∀ m', compatible p m' → run m' n c = some d) := by
  obtain ⟨t, ht, hc⟩ := child_cover p m (readSlot d) hcompatible hhole
  refine ⟨t, ht, hc, ?_⟩
  intro m' hm'
  rw [← common_prefix_of_partial_table p m m' c n hcompatible hm' hprefix]
  exact hseen

/-- Counting executed *ordinary* moves: if `n` moves produce `d`, then
    consulting an absent entry produces no successor at the next attempt.
    A separate convention bridge is necessary before this counts as the
    final Busy Beaver step. -/
theorem halting_entry (m : Machine) (c d : Config) (n : Nat)
    (hseen : run m n c = some d)
    (hhalt : m (readSlot d) = none) :
    run m (n+1) c = none := by
  simp [run, hseen, rawStep, hhalt]

#print axioms first_hole_branch
#print axioms halting_entry

end BB6Coverage

namespace BB6Coverage

/-- Proof-carrying coverage tree. A branch is permitted only at an
    unassigned transition; a leaf must prove the goal for every compatible
    concrete machine. This structure does not admit unproved discard nodes. -/
inductive Cover (good : Machine → Prop) : PartialMachine → Prop where
  | leaf (p : PartialMachine) (h : ∀ m, compatible p m → good m) : Cover good p
  | branch (p : PartialMachine) (s : Slot) (hu : p s = none)
      (kids : ∀ t, t ∈ choices → Cover good (refine p s t)) : Cover good p

theorem Cover.sound {good : Machine → Prop} {p : PartialMachine}
    (cert : Cover good p) : ∀ m, compatible p m → good m := by
  induction cert with
  | leaf p h => exact h
  | branch p s hu kids ih =>
    intro m hc
    obtain ⟨t, ht, htcomp⟩ := child_cover p m s hc hu
    exact ih t ht m htcomp

def emptyTable : PartialMachine := fun _ => none

theorem empty_compatible (m : Machine) : compatible emptyTable m := by
  intro s t h
  simp [emptyTable] at h

/-- A fully closed, kernel-checked 25-way coverage proof over the empty
    table would decide the specified predicate for EVERY six-state machine.
    Crucially, such a certificate has not been constructed for BB(6). -/
theorem global_coverage {good : Machine → Prop}
    (cert : Cover good emptyTable) : ∀ m : Machine, good m := by
  intro m
  exact cert.sound m (empty_compatible m)

def blank : Config :=
  { state := ⟨0, by decide⟩, head := 0, tape := fun _ => false }

/-- `HaltsAfter n` means `n` successful ordinary moves followed by a
    transition query with no successor. The external step-score convention
    must count this final halting query as one step to obtain score `n+1`. -/
def HaltsAfter (m : Machine) (n : Nat) : Prop :=
  (run m n blank).isSome = true ∧ run m (n+1) blank = none

def NeverHalts (m : Machine) : Prop :=
  ∀ n, (run m n blank).isSome = true

def DecidedBelow (bound : Nat) (m : Machine) : Prop :=
  NeverHalts m ∨ ∃ n, n+1 ≤ bound ∧ HaltsAfter m n

def Attainable (score : Nat) : Prop :=
  ∃ m n, HaltsAfter m n ∧ score = n+1

theorem run_none_add (m : Machine) (c : Config) (n k : Nat)
    (h : run m n c = none) : run m (n+k) c = none := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [Nat.add_succ]
    simp [run, ih]

theorem halting_time_unique (m : Machine) (n k : Nat)
    (hn : HaltsAfter m n) (hk : HaltsAfter m k) : n = k := by
  rcases Nat.lt_trichotomy n k with hlt | heq | hgt
  · obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hlt)
    have hnone : run m k blank = none := by
      rw [ht]
      exact run_none_add m blank (n+1) t hn.2
    simp [HaltsAfter, hnone] at hk
  · exact heq
  · obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hgt)
    have hnone : run m n blank = none := by
      rw [ht]
      exact run_none_add m blank (k+1) t hk.2
    simp [HaltsAfter, hnone] at hn

/-- Global upper-bound interface, contingent on a *complete* coverage
    certificate. No assumption about any specific holdout is hidden. -/
theorem maximal_runtime_if_cover (bound : Nat)
    (cert : Cover (DecidedBelow bound) emptyTable) :
    ∀ score, Attainable score → score ≤ bound := by
  intro score ⟨m,n,hh,heq⟩
  rcases global_coverage cert m with hnever | ⟨k, hbound, hk⟩
  · have hsome := hnever (n+1)
    simp [hh.2] at hsome
  · have hunique := halting_time_unique m n k hh hk
    subst k
    exact Nat.le_trans (by simp [heq]) hbound

#print axioms Cover.sound
#print axioms global_coverage
#print axioms halting_time_unique
#print axioms maximal_runtime_if_cover

/-- A precise upper-bound + witness interface. The required certificate and
    halting witness are both explicit parameters; supplying neither is not
    a proof of a numerical BB(6) value. -/
theorem exact_maximum_if_certificate (bound : Nat)
    (cert : Cover (DecidedBelow bound) emptyTable)
    (champ : Machine) (n : Nat)
    (hchamp : HaltsAfter champ n) (hscore : n+1 = bound) :
    Attainable bound ∧ ∀ score, Attainable score → score ≤ bound := by
  constructor
  · exact ⟨champ, n, hchamp, hscore.symm⟩
  · exact maximal_runtime_if_cover bound cert

#print axioms exact_maximum_if_certificate

/-- A real closed leaf: all tables that halt on the initial blank read. -/
def initialSlot : Slot := (⟨0, by decide⟩, false)
def immediateHalt : PartialMachine := refine emptyTable initialSlot none

theorem blank_reads_initial : readSlot blank = initialSlot := rfl

theorem immediate_halt_after_zero (m : Machine)
    (h : compatible immediateHalt m) : HaltsAfter m 0 := by
  have h0 : m initialSlot = none :=
    h initialSlot none (by simp [immediateHalt, refine])
  constructor
  · rfl
  · simp [run, rawStep, blank_reads_initial, h0]

theorem immediate_halt_leaf (bound : Nat) (hb : 1 ≤ bound) :
    Cover (DecidedBelow bound) immediateHalt := by
  apply Cover.leaf
  intro m hm
  exact Or.inr ⟨0, hb, immediate_halt_after_zero m hm⟩

#print axioms immediate_halt_leaf

end BB6Coverage
