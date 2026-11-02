import RankC

namespace BB6Rank

theorem nextC_critical_precursor {s s' : Nat × Nat × Nat}
    (h : nextC s = some s') (hc : s'.2.2 = 2) :
    s = (0, 0, 0) ∨ ∃ j : Nat, s = (0, 2 * j, 5) := by
  rcases s with ⟨a, k, c⟩
  rcases c with _ | _ | _ | _ | d
  · rcases a with _ | _ | a
    · simp only [nextC, Option.some.injEq] at h
      subst s'
      dsimp at hc
      have hk : k = 0 := by omega
      subst k
      exact Or.inl rfl
    · rcases k with _ | k
      · simp only [nextC, Option.some.injEq] at h
        subst s'
        simp at hc
      · simp only [nextC, Option.some.injEq] at h
        subst s'
        dsimp at hc
        omega
    · simp only [nextC, Option.some.injEq] at h
      subst s'
      dsimp at hc
      omega
  · simp only [nextC, Option.some.injEq] at h
    subst s'
    simp at hc
  · simp [nextC] at h
  · simp only [nextC, Option.some.injEq] at h
    subst s'
    simp at hc
  · rcases a with _ | a
    · dsimp [nextC] at h
      by_cases even : k % 2 = 0
      · simp only [even, ↓reduceIte, Option.some.injEq] at h
        subst s'
        dsimp at hc
        have hd : d = 1 := by omega
        have hk : k = 2 * (k / 2) := by omega
        subst d
        right
        exact ⟨k / 2, by rw [← hk]⟩
      · simp only [even, ↓reduceIte, Option.some.injEq] at h
        subst s'
        dsimp at hc
        omega
    · simp only [nextC, Option.some.injEq] at h
      subst s'
      dsimp at hc
      omega

end BB6Rank
