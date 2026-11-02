import Critical

namespace BB6Rank

/-- A basic monotonicity fact for the weighted potential. -/
theorem nextC_rank_monotone {s t : Nat × Nat × Nat}
    (h : nextC s = some t) : rankC s ≤ rankC t := by
  rcases nextC_lex_progress h with h | ⟨he, _⟩
  · omega
  · omega

theorem nextC_run_rank_monotone (n : Nat) (s t : Nat × Nat × Nat)
    (h : runSteps nextC n s = some t) : rankC s ≤ rankC t := by
  induction n generalizing t with
  | zero =>
      simp only [runSteps, Option.some.injEq] at h
      subst t
      exact Nat.le_refl _
  | succ n ih =>
      cases hs : runSteps nextC n s with
      | none => simp [runSteps, hs] at h
      | some mid =>
          simp only [runSteps, hs, Option.bind_some] at h
          have h1 := ih mid hs
          have h2 := nextC_rank_monotone h
          exact Nat.le_trans h1 h2

theorem nextC_zero_inaccessible (n : Nat) :
    runSteps nextC n (5,0,1) ≠ some (0,0,0) := by
  intro h
  have hh := nextC_run_rank_monotone n (5,0,1) (0,0,0) h
  simp [rankC] at hh

/-- Every reachable critical-level state c=2 has the unique accessible precursor family. -/
theorem nextC_halt_predecessor (n : Nat) (s : Nat × Nat × Nat)
    (h : runSteps nextC (n + 1) (5,0,1) = some s) (hc : s.2.2 = 2) :
    ∃ j, runSteps nextC n (5,0,1) = some (0,2*j,5) := by
  cases hs : runSteps nextC n (5,0,1) with
  | none => simp [runSteps, hs] at h
  | some mid =>
      simp only [runSteps, hs, Option.bind_some] at h
      rcases nextC_critical_precursor h hc with hzero | ⟨j, he⟩
      · subst mid
        exact False.elim (nextC_zero_inaccessible n hs)
      · subst mid
        exact ⟨j, rfl⟩

theorem nextC_none_iff (s : Nat × Nat × Nat) :
    nextC s = none ↔ s.2.2 = 2 := by
  rcases s with ⟨a,k,c⟩
  rcases c with _ | _ | _ | _ | d
  · rcases a with _ | _ | a
    · simp [nextC]
    · rcases k with _ | k <;> simp [nextC]
    · simp [nextC]
  · simp [nextC]
  · simp [nextC]
  · simp [nextC]
  · rcases a with _ | a
    · by_cases hk : k % 2 = 0
      · simp [nextC, hk]
      · simp [nextC, hk]
    · simp [nextC]

def CollatzStops {α : Type} (f : α → Option α) (x : α) : Prop :=
  ∃ n s, runSteps f n x = some s ∧ f s = none

/-- Exact reduction of this accelerator's halting problem to a single counter family. -/
theorem nextC_stops_iff_critical :
    CollatzStops nextC (5,0,1) ↔
      ∃ n j, runSteps nextC n (5,0,1) = some (0,2*j,5) := by
  constructor
  · rintro ⟨n, s, hs, hnone⟩
    have hc := (nextC_none_iff s).mp hnone
    rcases n with _ | n
    · simp only [runSteps, Option.some.injEq] at hs
      subst s
      simp at hc
    · rcases nextC_halt_predecessor n s hs hc with ⟨j, hprev⟩
      exact ⟨n, j, hprev⟩
  · rintro ⟨n, j, hprev⟩
    have step : nextC (0, 2*j, 5) = some (4*j+2,2,2) := by
      simp [nextC]
    have hit : runSteps nextC (n+1) (5,0,1) = some (4*j+2,2,2) := by
      simp only [runSteps, hprev, Option.bind_some]
      exact step
    exact ⟨n+1, (4*j+2,2,2), hit, by simp [nextC]⟩

end BB6Rank
