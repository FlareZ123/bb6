import Lean.Elab.Tactic.Omega

namespace BB6Rank

def nextA : Nat × Nat → Option (Nat × Nat)
  | (0, 0) => some (0, 2)
  | (0, k + 1) => some (2, k)
  | (1, _) => none
  | (m + 2, k) =>
      if m % 2 = 0 then
        some (3 * (m / 2) + k + 3, 1)
      else
        some (m / 2, m / 2 + k + 4)

def rankA (s : Nat × Nat) : Nat := s.1 + s.2

theorem nextA_rank_strict {s s' : Nat × Nat} (h : nextA s = some s') :
    rankA s < rankA s' := by
  rcases s with ⟨m, k⟩
  rcases m with _ | _ | n
  · rcases k with _ | k
    · simp only [nextA, Option.some.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp [rankA]
    · simp only [nextA, Option.some.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp only [rankA]
      omega
  · simp [nextA] at h
  · dsimp [nextA] at h
    by_cases even : n % 2 = 0
    · simp only [even, ↓reduceIte, Option.some.injEq] at h
      subst s'
      simp only [rankA]
      omega
    · simp only [even, ↓reduceIte, Option.some.injEq] at h
      subst s'
      simp only [rankA]
      omega

/-- A second formally published six-state machine's Collatz-like reduction. -/
def nextB : Nat × Nat × Nat → Option (Nat × Nat × Nat)
  | (0, 0, _) => none
  | (a + 1, 0, c) => some (a, c, 2)
  | (0, 1, c) => some (2 * c + 9, 0, 0)
  | (a + 1, 1, c) => some (a, c, 6)
  | (a, b + 2, c) => some (a, b, c + 3)

def rankB (s : Nat × Nat × Nat) : Nat := s.1 + s.2.1 + s.2.2

theorem nextB_rank_strict {s s' : Nat × Nat × Nat} (h : nextB s = some s') :
    rankB s < rankB s' := by
  rcases s with ⟨a, b, c⟩
  rcases b with _ | _ | b
  · rcases a with _ | a
    · simp [nextB] at h
    · simp only [nextB, Option.some.injEq] at h
      subst s'
      simp only [rankB]
      omega
  · rcases a with _ | a
    · simp only [nextB, Option.some.injEq] at h
      subst s'
      simp only [rankB]
      omega
    · simp only [nextB, Option.some.injEq] at h
      subst s'
      simp only [rankB]
      omega
  · simp only [nextB, Option.some.injEq] at h
    subst s'
    simp only [rankB]
    omega

/-- A partial deterministic dynamics; none means the orbit has halted. -/
def runSteps {α : Type} (f : α → Option α) : Nat → α → Option α
  | 0, s => some s
  | n + 1, s => (runSteps f n s).bind f

/-- A strict potential gives an unbounded integer lower bound on any surviving orbit. -/
theorem rank_growth {α : Type} (f : α → Option α) (rank : α → Nat)
    (increase : ∀ {x y}, f x = some y → rank x < rank y)
    (n : Nat) (x y : α) (h : runSteps f n x = some y) :
    rank x + n ≤ rank y := by
  induction n generalizing y with
  | zero =>
      simp only [runSteps, Option.some.injEq] at h
      subst y
      simp
  | succ n ih =>
      cases hm : runSteps f n x with
      | none => simp [runSteps, hm] at h
      | some mid =>
          simp only [runSteps, hm, Option.bind_some] at h
          have h1 := ih mid hm
          have h2 := increase h
          omega

/-- The first Collatz reduction's surviving orbit cannot repeat a state. -/
theorem nextA_no_repeat (n m : Nat) (s s' : Nat × Nat)
    (h : runSteps nextA (n + m + 1) s = some s') :
    rankA s < rankA s' := by
  have hh := rank_growth nextA rankA (fun {_ _} => nextA_rank_strict) (n+m+1) s s' h
  omega

/-- Unconditional (pre-halting) rank bound for the other published acceleration. -/
theorem nextB_growth (n : Nat) (s s' : Nat × Nat × Nat)
    (h : runSteps nextB n s = some s') : rankB s + n ≤ rankB s' :=
  rank_growth nextB rankB (fun {_ _} => nextB_rank_strict) n s s' h

end BB6Rank
