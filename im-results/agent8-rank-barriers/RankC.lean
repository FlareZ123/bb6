import RankCertificate

namespace BB6Rank

/-- Exact transcription of an accelerated three-counter BB(6) map. -/
def nextC : Nat × Nat × Nat → Option (Nat × Nat × Nat)
  | (a, k, 1) => some (a, k + 1, 0)
  | (_, _, 2) => none
  | (a, k, 3) => some (a, k + 2, 1)
  | (0, k, 0) => some (1, 0, 2 * k + 2)
  | (1, 0, 0) => some (5, 0, 1)
  | (1, k + 1, 0) => some (2, 2, 2 * k + 1)
  | (a + 2, k, 0) => some (a, 1, 2 * k + 1)
  | (0, k, d + 4) =>
      if k % 2 = 0 then
        some (4 * (k / 2) + 2, 2, d + 1)
      else
        some (4 * (k / 2) + 5, 0, d + 4)
  | (a + 1, k, d + 4) => some (a, k + 1, d + 3)

def rankC (s : Nat × Nat × Nat) : Nat := s.1 + 2 * s.2.1 + s.2.2

/-- The weighted potential grows, or is constant while the first counter falls. -/
theorem nextC_lex_progress {s s' : Nat × Nat × Nat}
    (h : nextC s = some s') :
    rankC s < rankC s' ∨ (rankC s = rankC s' ∧ s'.1 < s.1) := by
  rcases s with ⟨a, k, c⟩
  rcases c with _ | _ | _ | _ | d
  · rcases a with _ | _ | a
    · simp only [nextC, Option.some.injEq] at h
      subst s'
      left
      simp only [rankC]
      omega
    · rcases k with _ | k
      · simp only [nextC, Option.some.injEq] at h
        subst s'
        left
        simp only [rankC]
        omega
      · simp only [nextC, Option.some.injEq] at h
        subst s'
        left
        simp only [rankC]
        omega
    · simp only [nextC, Option.some.injEq] at h
      subst s'
      left
      simp only [rankC]
      omega
  · simp only [nextC, Option.some.injEq] at h
    subst s'
    left
    simp only [rankC]
    omega
  · simp [nextC] at h
  · simp only [nextC, Option.some.injEq] at h
    subst s'
    left
    simp only [rankC]
    omega
  · rcases a with _ | a
    · dsimp [nextC] at h
      by_cases even : k % 2 = 0
      · simp only [even, ↓reduceIte, Option.some.injEq] at h
        subst s'
        left
        simp only [rankC]
        omega
      · simp only [even, ↓reduceIte, Option.some.injEq] at h
        subst s'
        left
        simp only [rankC]
        omega
    · simp only [nextC, Option.some.injEq] at h
      subst s'
      right
      constructor
      · simp only [rankC]
        omega
      · omega

/-- Encode a lexicographic escape potential into a natural number. -/
def squarePotential (r a : Nat) : Nat := r * r + (r - a)

private theorem squarePotential_grows (r r' a a' : Nat)
    (ha : a ≤ r) (ha' : a' ≤ r')
    (h : r < r' ∨ (r = r' ∧ a' < a)) :
    squarePotential r a < squarePotential r' a' := by
  rcases h with h | ⟨he, hd⟩
  · have hm : (r + 1) * (r + 1) ≤ r' * r' :=
      Nat.mul_le_mul (Nat.succ_le_iff.mpr h) (Nat.succ_le_iff.mpr h)
    have hg : r * r + r < (r + 1) * (r + 1) := by
      simp only [Nat.add_mul, Nat.mul_add]
      omega
    simp only [squarePotential]
    omega
  · subst r'
    simp only [squarePotential]
    omega

/-- Strictly increasing scalar potential for every surviving third-machine step. -/
theorem nextC_squarePotential_strict {s s' : Nat × Nat × Nat}
    (h : nextC s = some s') :
    squarePotential (rankC s) s.1 < squarePotential (rankC s') s'.1 := by
  have hp := nextC_lex_progress h
  apply squarePotential_grows (rankC s) (rankC s') s.1 s'.1
  · rcases s with ⟨a, k, c⟩
    simp only [rankC]
    omega
  · rcases s' with ⟨a, k, c⟩
    simp only [rankC]
    omega
  · exact hp

/-- General quantitative escape bound for the third machine. -/
theorem nextC_growth (n : Nat) (s s' : Nat × Nat × Nat)
    (h : runSteps nextC n s = some s') :
    squarePotential (rankC s) s.1 + n ≤ squarePotential (rankC s') s'.1 :=
  rank_growth nextC (fun q => squarePotential (rankC q) q.1)
    (fun {_ _} => nextC_squarePotential_strict) n s s' h

/-- From the published initial state, any n surviving macro steps imply a quadratic rank bound. -/
theorem nextC_start_space_bound (n : Nat) (s' : Nat × Nat × Nat)
    (h : runSteps nextC n (5, 0, 1) = some s') :
    37 + n ≤ rankC s' * (rankC s' + 1) := by
  have h1 := nextC_growth n (5, 0, 1) s' h
  have h2 : s'.1 ≤ rankC s' := by
    rcases s' with ⟨a, k, c⟩
    simp only [rankC]
    omega
  have h3 : squarePotential (rankC s') s'.1 ≤ rankC s' * (rankC s' + 1) := by
    simp only [squarePotential, Nat.mul_add, Nat.mul_one]
    omega
  change 37 + n ≤ squarePotential (rankC s') s'.1 at h1
  omega

end BB6Rank
