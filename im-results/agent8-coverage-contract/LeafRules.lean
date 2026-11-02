import OneHalt

namespace BB6Coverage

/-- Exact composition of raw finite runs. -/
theorem run_add (m : Machine) (c : Config) (n k : Nat) :
    run m (n+k) c = (run m n c).bind (run m k) := by
  induction k with
  | zero =>
    simp [run]
  | succ k ih =>
    rw [Nat.add_succ, run, ih]
    cases h : run m n c with
    | none => simp
    | some d => rfl

/-- A genuine repeated complete configuration, with positive period, is a
    complete mathematical nonhalting certificate. -/
theorem cycle_never_halts_from (m : Machine) (d : Config) (p : Nat)
    (hp : 0 < p) (hcycle : run m p d = some d) :
    ∀ n, (run m n d).isSome = true := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hsmall : n ≤ p
    · exact run_some_prefix m d p n hsmall (by simp [hcycle])
    · have hle : p ≤ n := by omega
      obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le hle
      have hqsmall : q < n := by omega
      have hbefore := ih q hqsmall
      have heq : run m n d = run m q d := by
        rw [hq, run_add, hcycle]
        rfl
      simpa only [heq] using hbefore

/-- From a blank-tape finite entry into the cycle, all future run lengths
    remain defined; no empirical cutoff enters the proof. -/
theorem eventually_cycle_never (m : Machine) (d : Config) (k p : Nat)
    (hp : 0 < p) (hentry : run m k blank = some d)
    (hcycle : run m p d = some d) : NeverHalts m := by
  intro n
  by_cases hsmall : n ≤ k
  · exact run_some_prefix m blank k n hsmall (by simp [hentry])
  · have hle : k ≤ n := by omega
    obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le hle
    rw [hq, run_add, hentry]
    exact cycle_never_halts_from m d p hp hcycle q

/-- For a partial table, if the first n+1 consultations are all assigned,
    the exact halt time is valid for every compatible completion. -/
theorem halting_leaf (p : PartialMachine) (w : Machine) (n B : Nat)
    (hw : compatible p w)
    (known : ∀ k, k < n+1 → ∀ d, run w k blank = some d →
       p (readSlot d) = some (w (readSlot d)))
    (hh : HaltsAfter w n) (hbound : n+1 ≤ B) :
    Cover (DecidedBelow B) p := by
  apply Cover.leaf
  intro m hm
  right
  refine ⟨n, hbound, ?_⟩
  have hlong := common_prefix_of_partial_table p w m blank (n+1) hw hm known
  have hshort := common_prefix_of_partial_table p w m blank n hw hm
    (by intro k hk d hd; exact known k (Nat.lt_trans hk (Nat.lt_succ_self n)) d hd)
  unfold HaltsAfter at hh ⊢
  constructor
  · rw [← hshort]
    exact hh.1
  · rw [← hlong]
    exact hh.2

/-- A loop certificate valid for all completions must know every consulted
    slot along the entry and one full return cycle. -/
theorem cycle_leaf (p : PartialMachine) (w : Machine) (d : Config)
    (k period B : Nat)
    (hw : compatible p w)
    (hperiod : 0 < period)
    (hentry : run w k blank = some d)
    (hcycle : run w period d = some d)
    (knownEntry : ∀ i, i < k → ∀ x, run w i blank = some x →
       p (readSlot x) = some (w (readSlot x)))
    (knownCycle : ∀ i, i < period → ∀ x, run w i d = some x →
       p (readSlot x) = some (w (readSlot x))) :
    Cover (DecidedBelow B) p := by
  apply Cover.leaf
  intro m hm
  left
  have hentry' : run m k blank = some d := by
    rw [← common_prefix_of_partial_table p w m blank k hw hm knownEntry]
    exact hentry
  have hcycle' : run m period d = some d := by
    rw [← common_prefix_of_partial_table p w m d period hw hm knownCycle]
    exact hcycle
  exact eventually_cycle_never m d k period hperiod hentry' hcycle'

#print axioms run_add
#print axioms cycle_never_halts_from
#print axioms eventually_cycle_never
#print axioms halting_leaf
#print axioms cycle_leaf
end BB6Coverage
