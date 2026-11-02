import RayClosed

namespace BB6Coverage

def freshRight (c : Config) : Prop :=
  ∀ x : Int, c.head ≤ x → c.tape x = false

def freshLeft (c : Config) : Prop :=
  ∀ x : Int, x ≤ c.head → c.tape x = false

theorem freshRight_move (c : Config) (mv : Move)
    (hc : freshRight c) (hd : mv.right = true) :
    freshRight (applyMove c mv) := by
  intro x hx
  have hge : c.head ≤ x := by
    simp only [applyMove, hd, ite_true] at hx
    omega
  have hneq : x ≠ c.head := by
    simp only [applyMove, hd, ite_true] at hx
    omega
  simp [applyMove, hneq, hc x hge]

theorem freshLeft_move (c : Config) (mv : Move)
    (hc : freshLeft c) (hd : mv.right = false) :
    freshLeft (applyMove c mv) := by
  intro x hx
  have hh : (applyMove c mv).head = c.head-1 := by simp [applyMove, hd]; omega
  have hle : x ≤ c.head := by
    rw [hh] at hx
    omega
  have hneq : x ≠ c.head := by
    rw [hh] at hx
    omega
  simp [applyMove, hneq, hc x hle]

theorem freshRight_run (m : Machine) (S : Fin 6 → Prop)
    (hclosed : rightClosed m S) (c : Config)
    (hS : S c.state) (hf : freshRight c) (n : Nat) :
    ∃ d, run m n c = some d ∧ S d.state ∧ freshRight d := by
  induction n with
  | zero => exact ⟨c, rfl, hS, hf⟩
  | succ n ih =>
    obtain ⟨d, hd, hstate, hfree⟩ := ih
    obtain ⟨mv, hm, hright, hnext⟩ := hclosed d.state hstate
    have hslot : readSlot d = (d.state, false) := by
      have hz := hfree d.head (Int.le_refl _)
      exact Prod.ext rfl hz
    refine ⟨applyMove d mv, ?_, hnext, freshRight_move d mv hfree hright⟩
    simp only [run, hd, Option.bind_some, rawStep, hslot, hm, Option.map_some]

theorem freshLeft_run (m : Machine) (S : Fin 6 → Prop)
    (hclosed : leftClosed m S) (c : Config)
    (hS : S c.state) (hf : freshLeft c) (n : Nat) :
    ∃ d, run m n c = some d ∧ S d.state ∧ freshLeft d := by
  induction n with
  | zero => exact ⟨c, rfl, hS, hf⟩
  | succ n ih =>
    obtain ⟨d, hd, hstate, hfree⟩ := ih
    obtain ⟨mv, hm, hleft, hnext⟩ := hclosed d.state hstate
    have hslot : readSlot d = (d.state, false) := by
      have hz := hfree d.head (Int.le_refl _)
      exact Prod.ext rfl hz
    refine ⟨applyMove d mv, ?_, hnext, freshLeft_move d mv hfree hleft⟩
    simp only [run, hd, Option.bind_some, rawStep, hslot, hm, Option.map_some]

private theorem ray_run_add (m : Machine) (c : Config) (n k : Nat) :
    run m (n+k) c = (run m n c).bind (run m k) := by
  induction k with
  | zero => simp [run]
  | succ k ih =>
    rw [Nat.add_succ, run, ih]
    cases h : run m n c with
    | none => simp
    | some d => rfl

private theorem ray_run_defined_prefix (m : Machine) (c : Config) (n k : Nat)
    (hsmall : n ≤ k) (hf : (run m k c).isSome = true) :
    (run m n c).isSome = true := by
  obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le hsmall
  cases hn : run m n c with
  | none =>
    have : run m k c = none := by
      rw [hq, ray_run_add, hn]
      rfl
    simp [this] at hf
  | some d => rfl

theorem eventually_fresh_right_never (m : Machine) (S : Fin 6 → Prop)
    (k : Nat) (c : Config) (hentry : run m k blank = some c)
    (hstate : S c.state) (hfree : freshRight c)
    (hclosed : rightClosed m S) : NeverHalts m := by
  intro n
  by_cases hsmall : n ≤ k
  · exact ray_run_defined_prefix m blank n k hsmall (by simp [hentry])
  · have hle : k ≤ n := by omega
    obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le hle
    obtain ⟨d, hd, _, _⟩ := freshRight_run m S hclosed c hstate hfree q
    rw [hq, ray_run_add, hentry]
    simp [hd]

theorem eventually_fresh_left_never (m : Machine) (S : Fin 6 → Prop)
    (k : Nat) (c : Config) (hentry : run m k blank = some c)
    (hstate : S c.state) (hfree : freshLeft c)
    (hclosed : leftClosed m S) : NeverHalts m := by
  intro n
  by_cases hsmall : n ≤ k
  · exact ray_run_defined_prefix m blank n k hsmall (by simp [hentry])
  · have hle : k ≤ n := by omega
    obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le hle
    obtain ⟨d, hd, _, _⟩ := freshLeft_run m S hclosed c hstate hfree q
    rw [hq, ray_run_add, hentry]
    simp [hd]

/-- A finite, fully assigned entry trace into a clean ray and an assigned
    closed-state tail is a nonhalting certificate for all completions. -/
theorem right_entry_leaf (p : PartialMachine) (w : Machine) (S : Fin 6 → Prop)
    (k : Nat) (c : Config) (bound : Nat) (hw : compatible p w)
    (hentry : run w k blank = some c)
    (hknown : ∀ i, i < k → ∀ d, run w i blank = some d →
      p (readSlot d) = some (w (readSlot d)))
    (hs : S c.state) (hf : freshRight c)
    (hclosed : ∀ s, S s → ∃ mv : Move,
      p (s, false) = some (some mv) ∧ mv.right = true ∧ S mv.next) :
    Cover (DecidedBelow bound) p := by
  apply Cover.leaf
  intro m hm
  left
  have hentry' : run m k blank = some c := by
    rw [← common_prefix_of_partial_table p w m blank k hw hm hknown]
    exact hentry
  apply eventually_fresh_right_never m S k c hentry' hs hf
  intro s hs'
  obtain ⟨mv, hp, hdir, hn⟩ := hclosed s hs'
  exact ⟨mv, hm (s,false) (some mv) hp, hdir, hn⟩

theorem left_entry_leaf (p : PartialMachine) (w : Machine) (S : Fin 6 → Prop)
    (k : Nat) (c : Config) (bound : Nat) (hw : compatible p w)
    (hentry : run w k blank = some c)
    (hknown : ∀ i, i < k → ∀ d, run w i blank = some d →
      p (readSlot d) = some (w (readSlot d)))
    (hs : S c.state) (hf : freshLeft c)
    (hclosed : ∀ s, S s → ∃ mv : Move,
      p (s, false) = some (some mv) ∧ mv.right = false ∧ S mv.next) :
    Cover (DecidedBelow bound) p := by
  apply Cover.leaf
  intro m hm
  left
  have hentry' : run m k blank = some c := by
    rw [← common_prefix_of_partial_table p w m blank k hw hm hknown]
    exact hentry
  apply eventually_fresh_left_never m S k c hentry' hs hf
  intro s hs'
  obtain ⟨mv, hp, hdir, hn⟩ := hclosed s hs'
  exact ⟨mv, hm (s,false) (some mv) hp, hdir, hn⟩

#print axioms eventually_fresh_right_never
#print axioms eventually_fresh_left_never
#print axioms right_entry_leaf
#print axioms left_entry_leaf
end BB6Coverage
