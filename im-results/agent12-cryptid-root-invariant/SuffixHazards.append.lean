/-!
Two short, uniform halting suffixes. These are prepared-configuration
hazards, not claims that either authentic root reaches them.
Append after TokenCounterCorrection.append.lean inside the source namespace.
-/

private theorem a12EL_zero (L R : List (ℕ × ℕ)) :
    ReachesPlus target (cfg_EL_n_n L ((0,0)::R))
      (cfg_EL_n_n ((0,0)::L) R) := by
  unfold cfg_EL_n_n
  rw [encLeft_d0_s0, encRight_d0_s0]
  execute 2

private theorem a12G_prefix (T : List (ℕ × ℕ)) :
    ReachesPlus target (cfg_CR_n_n [(0,0)] ((0,0)::T))
      (cfg_EL_n_n [(0,0),(1,0)] ((0,0)::(0,0)::T)) := by
  unfold cfg_CR_n_n cfg_EL_n_n
  simp only [encRight_d0_s0, encRight_d1_s0, encRight_nil, encLeft_d0_s0]
  execute 21

private theorem a12EL_sweep (k : ℕ) (L R : List (ℕ × ℕ)) :
    ReachesPlus target (cfg_EL_n_n L (List.replicate (k+1) (0,0) ++ R))
      (cfg_EL_n_n (List.replicate (k+1) (0,0) ++ L) R) := by
  induction k generalizing L with
  | zero => simpa using a12EL_zero L R
  | succ k ih =>
    have h1 := a12EL_zero L (List.replicate (k+1) (0,0) ++ R)
    have h2 := ih ((0,0)::L)
    have h3 := ReachesPlus.trans h1 h2
    rw [a12_rep_push (0,0) (k+1) L] at h3
    exact h3

/-- Any untouched left tail is allowed. -/
theorem a12EL_hazard111 (L : List (ℕ × ℕ)) :
    ∃ c, ReachesPlus target (cfg_EL_n_n ((0,0)::L) [(1,0),(1,0),(1,0)]) c ∧
      (step target c).isNone := by
  have h : ReachesPlus target
      (cfg_EL_n_n ((0,0)::L) [(1,0),(1,0),(1,0)])
      (tok_CR [1,1,1,1,0] [] (2::L.map Prod.fst)) := by
    unfold cfg_EL_n_n tok_CR
    rw [encRight_d0_s0, encRight_eq_nat L]
    simp only [encLeft_d1_s0, encLeft_nil]
    texecute 65
  obtain ⟨c,hc,hh⟩ := tok_CR_add2_halts [1,1,1,1,0] [] 0 (L.map Prod.fst)
  exact ⟨c,ReachesPlus.trans h hc,hh⟩

/-- Two zeros of left framing suffice; the remaining tail is arbitrary. -/
theorem a12EL_hazard1011 (L : List (ℕ × ℕ)) :
    ∃ c, ReachesPlus target (cfg_EL_n_n ((0,0)::(0,0)::L) [(1,0),(0,0),(1,0),(1,0)]) c ∧
      (step target c).isNone := by
  have h : ReachesPlus target
      (cfg_EL_n_n ((0,0)::(0,0)::L) [(1,0),(0,0),(1,0),(1,0)])
      (cfg_CR_n_n ((2,0)::L) [(12,0)]) := by
    unfold cfg_EL_n_n cfg_CR_n_n
    simp only [encRight_d0_s0, encLeft_d0_s0, encLeft_d1_s0, encLeft_nil]
    rw [encRight_succ 1 0 L, encRight_d1_s0]
    rw [encLeft_succ 11 0 [],
      encLeft_succ 10 0 [],
      encLeft_succ 9 0 [],
      encLeft_succ 8 0 [],
      encLeft_succ 7 0 [],
      encLeft_succ 6 0 [],
      encLeft_succ 5 0 [],
      encLeft_succ 4 0 [],
      encLeft_succ 3 0 [],
      encLeft_succ 2 0 [],
      encLeft_succ 1 0 [], encLeft_d1_s0 [], encLeft_nil]
    execute 113
  obtain ⟨c,hc,hh⟩ := tok_CR_add2_halts [] [(12,0)] 0 (L.map Prod.fst)
  have hc' : ReachesPlus target (cfg_CR_n_n ((2,0)::L) [(12,0)]) c := by
    simpa only [tok_CR, cfg_CR_n_n, encTokens_nil, encRight_eq_nat, List.map_cons, Prod.fst] using hc
  exact ⟨c,ReachesPlus.trans h hc',hh⟩

theorem a12G_to_EL (k : ℕ) (R : List (ℕ × ℕ)) :
    ReachesPlus target (cfg_CR_n_n [(0,0)] (List.replicate (k+1) (0,0) ++ R))
      (cfg_EL_n_n (List.replicate (k+3) (0,0) ++ [(1,0)]) R) := by
  have h1 := a12G_prefix (List.replicate k (0,0) ++ R)
  have h2 := a12EL_sweep (k+1) [(0,0),(1,0)] R
  rw [a12_rep_push (0,0) (k+2) [(1,0)]] at h2
  exact ReachesPlus.trans h1 h2

theorem a12G_hazard111 (k : ℕ) :
    ∃ c, ReachesPlus target (cfg_CR_n_n [(0,0)]
       (List.replicate (k+1) (0,0) ++ [(1,0),(1,0),(1,0)])) c ∧
      (step target c).isNone := by
  have h := a12G_to_EL k [(1,0),(1,0),(1,0)]
  obtain ⟨c,hc,hh⟩ := a12EL_hazard111 (List.replicate (k+2) (0,0) ++ [(1,0)])
  exact ⟨c,ReachesPlus.trans h hc,hh⟩

theorem a12G_hazard1011 (k : ℕ) :
    ∃ c, ReachesPlus target (cfg_CR_n_n [(0,0)]
       (List.replicate (k+1) (0,0) ++ [(1,0),(0,0),(1,0),(1,0)])) c ∧
      (step target c).isNone := by
  have h := a12G_to_EL k [(1,0),(0,0),(1,0),(1,0)]
  obtain ⟨c,hc,hh⟩ := a12EL_hazard1011 (List.replicate (k+1) (0,0) ++ [(1,0)])
  exact ⟨c,ReachesPlus.trans h hc,hh⟩

#print axioms a12EL_hazard111
#print axioms a12EL_hazard1011
#print axioms a12G_to_EL
#print axioms a12G_hazard111
#print axioms a12G_hazard1011
