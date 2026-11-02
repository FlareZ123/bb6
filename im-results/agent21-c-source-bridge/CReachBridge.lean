import CLine

namespace BB6.CReachBridge

abbrev S := Nat × Nat × Nat
abbrev start : S := (5,0,1)

def stepC (s : Option S) : Option S := s.bind BB6CLine.nextC

def runN : Nat → Option S → Option S
  | 0, s => s
  | n+1, s => stepC (runN n s)

def RunHalts : Prop := ∃ n : Nat, (runN n (some start)).isNone

/-- Finite iteration commutes with one step of its own transition function. -/
theorem runN_step_commute (n : Nat) (s : Option S) :
    runN n (stepC s) = stepC (runN n s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change stepC (runN n (stepC s)) = stepC (stepC (runN n s))
      rw [ih]

/-- Both tail-recursive conventions for finite iteration are equal. -/
theorem runN_succ_head (n : Nat) (s : Option S) :
    runN (n+1) s = runN n (stepC s) := by
  change stepC (runN n s) = runN n (stepC s)
  exact (runN_step_commute n s).symm

theorem reachable_of_run (n : Nat) (s : S)
    (h : runN n (some start) = some s) : BB6CLine.Reach s := by
  induction n generalizing s with
  | zero =>
      simp [runN] at h
      subst s
      exact BB6CLine.Reach.init
  | succ n ih =>
      change (runN n (some start)).bind BB6CLine.nextC = some s at h
      cases hp : runN n (some start) with
      | none => simp [hp] at h
      | some p =>
          rw [hp] at h
          change BB6CLine.nextC p = some s at h
          exact BB6CLine.Reach.next p s (ih p hp) h

theorem run_of_reachable {s : S} (h : BB6CLine.Reach s) :
    ∃ n, runN n (some start) = some s := by
  induction h with
  | init => exact ⟨0, rfl⟩
  | next s t hs hnext ih =>
      rcases ih with ⟨n, hn⟩
      refine ⟨n+1, ?_⟩
      simp [runN, stepC, hn, hnext]

theorem stop_of_run (n : Nat)
    (h : (runN n (some start)).isNone) :
    ∃ s, BB6CLine.Reach s ∧ BB6CLine.nextC s = none := by
  induction n with
  | zero => simp [runN] at h
  | succ n ih =>
      change ((runN n (some start)).bind BB6CLine.nextC).isNone at h
      cases hp : runN n (some start) with
      | none =>
          exact ih (by simp [hp])
      | some s =>
          rw [hp] at h
          change (BB6CLine.nextC s).isNone at h
          cases hn : BB6CLine.nextC s with
          | none => exact ⟨s, reachable_of_run n s hp, hn⟩
          | some t => simp [hn] at h

theorem runHalts_iff_reachable_stop :
    RunHalts ↔ ∃ s, BB6CLine.Reach s ∧ BB6CLine.nextC s = none := by
  constructor
  · rintro ⟨n, hn⟩
    exact stop_of_run n hn
  · rintro ⟨s, hr, hs⟩
    obtain ⟨n, hn⟩ := run_of_reachable hr
    refine ⟨n+1, ?_⟩
    simp [runN, stepC, hn, hs]

#print axioms runHalts_iff_reachable_stop
end BB6.CReachBridge
