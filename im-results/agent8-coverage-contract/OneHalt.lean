import Frontier

namespace BB6Coverage

/-- Safe arbitrary nonhalting completion for all halting entries other than
    the one that the given blank computation actually encounters. -/
def fallbackMove : Move :=
  {write := false, right := true, next := ⟨0, by decide⟩}

def isolateHalt (m : Machine) (s : Slot) : Machine := fun x =>
  if x = s then none else some ((m x).getD fallbackMove)

/-- The completed table has precisely one missing transition. -/
theorem isolateHalt_missing_iff (m : Machine) (s x : Slot) :
    isolateHalt m s x = none ↔ x = s := by
  by_cases hx : x = s
  · simp [isolateHalt, hx]
  · simp [isolateHalt, hx]

/-- Every already-defined transition away from the selected halting slot
    survives completion exactly, including its write, move, and successor. -/
theorem isolateHalt_preserves (m : Machine) (s x : Slot) (t : Move)
    (h : m x = some t) (hneq : x ≠ s) :
    isolateHalt m s x = some t := by
  simp [isolateHalt, hneq, h]

/-- A successful finite trace at length n forces every shorter trace to have
    been successful as well. -/
theorem run_some_prefix (m : Machine) (c : Config) (n k : Nat)
    (hk : k ≤ n) (h : (run m n c).isSome = true) :
    (run m k c).isSome = true := by
  cases hstate : run m k c with
  | some d => simp
  | none =>
    obtain ⟨d, heq⟩ := Nat.exists_eq_add_of_le hk
    have hnone : run m n c = none := by
      rw [heq]
      exact run_none_add m c k d hstate
    simp [hnone] at h

/-- Every consulted transition before the first halt was an ordinary move. -/
theorem defined_before_halt (m : Machine) (c : Config) (n k : Nat)
    (hk : k < n) (hn : (run m n c).isSome = true)
    (d : Config) (hseen : run m k c = some d) :
    ∃ t, m (readSlot d) = some t := by
  have hnext := run_some_prefix m c n (k+1) (Nat.succ_le_of_lt hk) hn
  simp only [run, hseen, Option.bind_some, rawStep] at hnext
  cases h : m (readSlot d) with
  | none => simp [h] at hnext
  | some t => exact ⟨t, rfl⟩

/-- Exact one-halt-entry normal form for any original halting blank run.
    Crucially, the halting entry is chosen from the *actual* n-th state, and
    no other absent entry could have been consulted before that time. -/
theorem one_halt_normal_form (m : Machine) (n : Nat)
    (hh : HaltsAfter m n) :
    ∃ s m',
      (∀ x, m' x = none ↔ x = s) ∧
      HaltsAfter m' n := by
  rcases hh with ⟨hseen, hnext⟩
  cases hn : run m n blank with
  | none => simp [hn] at hseen
  | some d =>
    let s := readSlot d
    let m' := isolateHalt m s
    have hterminal : m s = none := by
      simp only [run, hn, Option.bind_some, rawStep] at hnext
      cases h : m s with
      | none => rfl
      | some t => simp [s, h] at hnext
    have hprefix : ∀ k, k < n → ∀ x, run m k blank = some x →
        m (readSlot x) = m' (readSlot x) := by
      intro k hk x hx
      obtain ⟨t, ht⟩ := defined_before_halt m blank n k hk (by simp [hn]) x hx
      have hneq : readSlot x ≠ s := by
        intro heq
        rw [heq, hterminal] at ht
        contradiction
      have hpres := isolateHalt_preserves m s (readSlot x) t ht hneq
      exact ht.trans hpres.symm
    have hsame := run_agrees_on_prefix m m' blank n hprefix
    refine ⟨s,m',?_,?_⟩
    · intro x
      exact isolateHalt_missing_iff m s x
    · unfold HaltsAfter
      constructor
      · rw [← hsame, hn]
        rfl
      · rw [run]
        rw [← hsame, hn]
        simp [rawStep, m', isolateHalt, s]

/-- The one-halt subset suffices to bound ALL original six-state halting
    runtimes. This remains conditional on a proof of the subset's bound. -/
theorem one_halt_upper_bound (B : Nat)
    (h : ∀ m : Machine, (∃ s, ∀ x, m x = none ↔ x = s) →
      ∀ n, HaltsAfter m n → n+1 ≤ B) :
    ∀ m n, HaltsAfter m n → n+1 ≤ B := by
  intro m n hm
  obtain ⟨s,m',hunique,hhalts⟩ := one_halt_normal_form m n hm
  exact h m' ⟨s,hunique⟩ n hhalts

#print axioms isolateHalt_missing_iff
#print axioms defined_before_halt
#print axioms one_halt_normal_form
#print axioms one_halt_upper_bound
end BB6Coverage
