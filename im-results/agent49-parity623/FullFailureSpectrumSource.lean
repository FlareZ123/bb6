import Agent49FlatDrainSource

/-!
A complete finite first-counter failure spectrum for every positive B-block count,
with no b ≤ 3^a restriction. The theorem imports the original-source-proved
flatB_eq_drainB, hence refers to the exact Cryptids #623 B-drain.
It does not decide the authentic blank-root orbit.
-/
namespace BB6.Agent49FullSpectrum

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49FlatDrainSource

/-- This complete halting predicate uses only the first and block counters.
Every recursive block count is strictly smaller. -/
def badAll (a b : Nat) : Bool :=
  if b=0 then false
  else if b%3=0 then badAll (a+1) (b/3-1)
  else if b%3=1 then
    if a=0 then true else badAll (a-1) (b/3)
  else if a=0 then badAll 0 (b/3)
  else badAll (a-1) (b/3+1)
termination_by b
decreasing_by all_goals omega

theorem flat_failure (b : Nat) :
    ∀ a d, (flatB a b d = none) ↔ badAll a b = true := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a d
    rw [flatB,badAll]
    by_cases hz : b=0
    · simp [hz]
    · simp only [if_neg hz]
      by_cases h0 : b%3=0
      · simp only [if_pos h0]
        exact ih (b/3-1) (by omega) (a+1) (d+2*b+3)
      · simp only [if_neg h0]
        by_cases h1 : b%3=1
        · simp only [if_pos h1]
          by_cases ha : a=0
          · simp [ha]
          · simpa only [if_neg ha] using ih (b/3) (by omega) (a-1) (d+2*b+5)
        · simp only [if_neg h1]
          by_cases ha : a=0
          · simpa only [if_pos ha] using ih (b/3) (by omega) 0 (d+2*b+3)
          · simpa only [if_neg ha] using ih (b/3+1) (by omega) (a-1) (d+2*b+1)

/-- Every first counter at least as large as the block count is safe. -/
theorem flat_safe_ge (b : Nat) :
    ∀ a d, b ≤ a → flatB a b d ≠ none := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a d ha
    rw [flatB]
    by_cases hz : b=0
    · simp [hz]
    · simp only [if_neg hz]
      by_cases h0 : b%3=0
      · simp only [if_pos h0]
        exact ih (b/3-1) (by omega) (a+1) (d+2*b+3) (by omega)
      · simp only [if_neg h0]
        by_cases h1 : b%3=1
        · simp only [if_pos h1]
          have haz : a ≠ 0 := by omega
          simp only [if_neg haz]
          exact ih (b/3) (by omega) (a-1) (d+2*b+5) (by omega)
        · simp only [if_neg h1]
          have haz : a ≠ 0 := by omega
          simp only [if_neg haz]
          exact ih (b/3+1) (by omega) (a-1) (d+2*b+1) (by omega)

/-- An explicit finite, exhaustive list of every fatal first-counter value
for a fixed block count b. The list is independent of d. -/
def failures (b : Nat) : List Nat :=
  (List.range b).filter (fun a => badAll a b)

theorem flat_failure_spectrum (a b d : Nat) :
    (flatB a b d = none) ↔ a ∈ failures b := by
  rw [flat_failure b a d]
  simp only [failures, List.mem_filter, List.mem_range]
  constructor
  · intro h
    have hl : a < b := by
      by_cases ht : a < b
      · exact ht
      · have hs := flat_safe_ge b a d (by omega)
        exact False.elim (hs ((flat_failure b a d).2 h))
    exact ⟨hl,h⟩
  · intro h
    exact h.2

/-- Exact original-source all-counter failure test, without input bounds. -/
theorem drain_none_iff_badAll (a b d : Nat) :
    (drainB a b d = none) ↔ badAll a b = true := by
  rw [←flatB_eq_drainB b a d]
  exact flat_failure b a d

/-- For any fixed block count, every and only first-counter failure is
enumerated in the finite list. This is an all-Nat source theorem. -/
theorem drain_none_iff_failure_spectrum (a b d : Nat) :
    (drainB a b d = none) ↔ a ∈ failures b := by
  rw [←flatB_eq_drainB b a d]
  exact flat_failure_spectrum a b d

/-- Exact dependence on a,b alone: changing the third counter cannot affect
whether this drain halts. -/
theorem drain_failure_independent_d (a b d e : Nat) :
    (drainB a b d = none) ↔ (drainB a b e = none) := by
  rw [drain_none_iff_badAll, drain_none_iff_badAll]

#print axioms drain_none_iff_failure_spectrum
#print axioms drain_failure_independent_d
end BB6.Agent49FullSpectrum
