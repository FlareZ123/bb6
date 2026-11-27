/-!
Uniform regular-language halting families, from arbitrary binary prefixes.
Append after SuffixHazards.append.lean.
-/

private theorem a12EL_one (L R : List (ℕ × ℕ)) :
    ReachesPlus target (cfg_EL_n_n ((0,0)::L) ((1,0)::R))
      (cfg_EL_n_n ((0,0)::(1,0)::L) R) := by
  unfold cfg_EL_n_n
  simp only [encRight_d0_s0, encRight_d1_s0, encLeft_d1_s0]
  execute 7

/-- Source stack words containing only first-coordinate zero and one. -/
def a12Binary (w : List Bool) : List (ℕ × ℕ) :=
  w.map fun b => (if b then 1 else 0,0)

private theorem a12EL_prefix_halts
    (S : List (ℕ × ℕ))
    (h : ∀ L : List (ℕ × ℕ), ∃ c,
      ReachesPlus target (cfg_EL_n_n ((0,0)::L) S) c ∧ (step target c).isNone)
    (w : List Bool) (L : List (ℕ × ℕ)) :
    ∃ c, ReachesPlus target
      (cfg_EL_n_n ((0,0)::L) (a12Binary w ++ S)) c ∧
      (step target c).isNone := by
  induction w generalizing L with
  | nil => simpa [a12Binary] using h L
  | cons b w ih =>
    cases b
    · obtain ⟨c,hc,hh⟩ := ih ((0,0)::L)
      have h0 := a12EL_zero ((0,0)::L) (a12Binary w ++ S)
      exact ⟨c,ReachesPlus.trans h0 hc,hh⟩
    · obtain ⟨c,hc,hh⟩ := ih ((1,0)::L)
      have h1 := a12EL_one L (a12Binary w ++ S)
      exact ⟨c,ReachesPlus.trans h1 hc,hh⟩

theorem a12EL_binary_111_halts (w : List Bool) (L : List (ℕ × ℕ)) :
    ∃ c, ReachesPlus target
      (cfg_EL_n_n ((0,0)::L) (a12Binary w ++ [(1,0),(1,0),(1,0)])) c ∧
      (step target c).isNone :=
  a12EL_prefix_halts [(1,0),(1,0),(1,0)] a12EL_hazard111 w L

private theorem a12EL_01011_halts (L : List (ℕ × ℕ)) :
    ∃ c, ReachesPlus target
      (cfg_EL_n_n ((0,0)::L) [(0,0),(1,0),(0,0),(1,0),(1,0)]) c ∧
      (step target c).isNone := by
  have h0 := a12EL_zero ((0,0)::L) [(1,0),(0,0),(1,0),(1,0)]
  obtain ⟨c,hc,hh⟩ := a12EL_hazard1011 L
  exact ⟨c,ReachesPlus.trans h0 hc,hh⟩

theorem a12EL_binary_01011_halts (w : List Bool) (L : List (ℕ × ℕ)) :
    ∃ c, ReachesPlus target
      (cfg_EL_n_n ((0,0)::L)
        (a12Binary w ++ [(0,0),(1,0),(0,0),(1,0),(1,0)])) c ∧
      (step target c).isNone :=
  a12EL_prefix_halts [(0,0),(1,0),(0,0),(1,0),(1,0)] a12EL_01011_halts w L

theorem a12G_binary_111_halts (k : ℕ) (w : List Bool) :
    ∃ c, ReachesPlus target
      (cfg_CR_n_n [(0,0)] (List.replicate (k+1) (0,0) ++
        (a12Binary w ++ [(1,0),(1,0),(1,0)]))) c ∧
      (step target c).isNone := by
  have h := a12G_to_EL k (a12Binary w ++ [(1,0),(1,0),(1,0)])
  obtain ⟨c,hc,hh⟩ := a12EL_binary_111_halts w
    (List.replicate (k+2) (0,0) ++ [(1,0)])
  exact ⟨c,ReachesPlus.trans h hc,hh⟩

theorem a12G_binary_01011_halts (k : ℕ) (w : List Bool) :
    ∃ c, ReachesPlus target
      (cfg_CR_n_n [(0,0)] (List.replicate (k+1) (0,0) ++
        (a12Binary w ++ [(0,0),(1,0),(0,0),(1,0),(1,0)]))) c ∧
      (step target c).isNone := by
  have h := a12G_to_EL k (a12Binary w ++ [(0,0),(1,0),(0,0),(1,0),(1,0)])
  obtain ⟨c,hc,hh⟩ := a12EL_binary_01011_halts w
    (List.replicate (k+2) (0,0) ++ [(1,0)])
  exact ⟨c,ReachesPlus.trans h hc,hh⟩

#print axioms a12G_binary_111_halts
#print axioms a12G_binary_01011_halts
