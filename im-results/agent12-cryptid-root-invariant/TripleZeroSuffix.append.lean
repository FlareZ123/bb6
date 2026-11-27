/-!
A triple of consecutive one-valued pairs on the CR stack is fatal
when the opposite head is at least two. This extends the binary
suffix obstruction from 111 to 1110*.
-/
private theorem a12CR_high_halts (a : ℕ) (L R : List (ℕ × ℕ)) :
    ∃ c, ReachesPlus target (cfg_CR_n_n ((a+2,0)::L) R) c ∧
      (step target c).isNone := by
  obtain ⟨c,hc,hh⟩ := tok_CR_add2_halts [] R a (L.map Prod.fst)
  have he : tok_CR [] R ((a+2)::L.map Prod.fst) =
      cfg_CR_n_n ((a+2,0)::L) R := by
    simp only [tok_CR, cfg_CR_n_n, encTokens_nil, encRight_eq_nat,
      List.map_cons, Prod.fst]
  rw [he] at hc
  exact ⟨c,hc,hh⟩

private theorem a12CR_triple_high (a : ℕ) (L R : List (ℕ × ℕ)) :
    ∃ c, ReachesPlus target
      (cfg_CR_n_n ((1,0)::(1,0)::(1,0)::L) ((a+3,0)::R)) c ∧
      (step target c).isNone := by
  have h : ReachesPlus target
      (cfg_CR_n_n ((1,0)::(1,0)::(1,0)::L) ((a+3,0)::R))
      (cfg_CR_n_n ((2,0)::L) (List.replicate 4 (0,0) ++ (a,0)::R)) := by
    unfold cfg_CR_n_n
    simp only [List.replicate_succ, List.replicate_zero, List.cons_append,
      List.nil_append, encRight_d1_s0, encLeft_d0_s0]
    rw [encRight_succ 1 0 L, encRight_d1_s0 L,
      encLeft_succ (a+2) 0 R, encLeft_succ (a+1) 0 R,
      encLeft_succ a 0 R, encLeft_run_s0 a R]
    execute 41
  obtain ⟨c,hc,hh⟩ := a12CR_high_halts 0 L
    (List.replicate 4 (0,0) ++ (a,0)::R)
  exact ⟨c,ReachesPlus.trans h hc,hh⟩

private theorem a12CR_triple_two (L R : List (ℕ × ℕ)) :
    ∃ c, ReachesPlus target
      (cfg_CR_n_n ((1,0)::(1,0)::(1,0)::L) ((2,0)::R)) c ∧
      (step target c).isNone := by
  have h : ReachesPlus target
      (cfg_CR_n_n ((1,0)::(1,0)::(1,0)::L) ((2,0)::R))
      (tok_CR [1,1,1,1,0] R (2::L.map Prod.fst)) := by
    unfold cfg_CR_n_n tok_CR
    simp only [encRight_d1_s0]
    rw [encRight_eq_nat L, encLeft_succ 1 0 R, encLeft_d1_s0 R]
    texecute 41
  obtain ⟨c,hc,hh⟩ := tok_CR_add2_halts [1,1,1,1,0] R 0 (L.map Prod.fst)
  exact ⟨c,ReachesPlus.trans h hc,hh⟩

theorem a12CR_triple_positive (a : ℕ) (L R : List (ℕ × ℕ)) :
    ∃ c, ReachesPlus target
      (cfg_CR_n_n ((1,0)::(1,0)::(1,0)::L) ((a+2,0)::R)) c ∧
      (step target c).isNone := by
  cases a with
  | zero => exact a12CR_triple_two L R
  | succ a => exact a12CR_triple_high a L R

private theorem a12CR_zero_pair (b : ℕ) (L R : List (ℕ × ℕ)) :
    ReachesPlus target (cfg_CR_n_n ((0,0)::L) ((b,0)::R))
      (cfg_CR_n_n L ((b+2,0)::R)) := by
  unfold cfg_CR_n_n
  rw [encRight_d0_s0 L, encLeft_succ (b+1) 0 R, encLeft_succ b 0 R]
  execute 2

private theorem a12CR_zero_sweep (k b : ℕ) (L R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_CR_n_n (List.replicate (k+1) (0,0) ++ L) ((b,0)::R))
      (cfg_CR_n_n L ((b+2*(k+1),0)::R)) := by
  induction k generalizing b with
  | zero => simpa using a12CR_zero_pair b L R
  | succ k ih =>
    have h1 := a12CR_zero_pair b (List.replicate (k+1) (0,0) ++ L) R
    have h2 := ih (b+2)
    have he : b+2+2*(k+1) = b+2*(k+2) := by omega
    rw [he] at h2
    exact ReachesPlus.trans h1 h2

private theorem a12EL_empty (L : List (ℕ × ℕ)) :
    ReachesPlus target (cfg_EL_n_n L []) (cfg_CR_n_n L [(0,0)]) := by
  unfold cfg_EL_n_n cfg_CR_n_n
  rw [encLeft_d0_s0 []]
  execute 1

private theorem a12EL_triple_collect (g : ℕ) (L : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_EL_n_n ((0,0)::L)
        ([(1,0),(1,0),(1,0)] ++ List.replicate g (0,0)))
      (cfg_CR_n_n ((1,0)::(1,0)::(1,0)::L) [(2*(g+1),0)]) := by
  let T := List.replicate g (0,0)
  let LL := (1,0)::(1,0)::(1,0)::L
  have h1 := a12EL_one L ((1,0)::(1,0)::T)
  have h2 := a12EL_one ((1,0)::L) ((1,0)::T)
  have h3 := a12EL_one ((1,0)::(1,0)::L) T
  have h := ReachesPlus.trans h1 (ReachesPlus.trans h2 h3)
  have h4 : ReachesPlus target (cfg_EL_n_n ((0,0)::LL) T)
      (cfg_CR_n_n (List.replicate (g+1) (0,0) ++ LL) [(0,0)]) := by
    cases g with
    | zero => exact a12EL_empty ((0,0)::LL)
    | succ k =>
      have hs := a12EL_sweep k ((0,0)::LL) []
      rw [List.append_nil, a12_rep_push (0,0) (k+1) LL] at hs
      exact ReachesPlus.trans hs (a12EL_empty _)
  have h5 := a12CR_zero_sweep g 0 LL []
  simp only [Nat.zero_add] at h5
  exact ReachesPlus.trans h (ReachesPlus.trans h4 h5)

theorem a12EL_triple_zeros_halts (g : ℕ) (L : List (ℕ × ℕ)) :
    ∃ c, ReachesPlus target
      (cfg_EL_n_n ((0,0)::L)
        ([(1,0),(1,0),(1,0)] ++ List.replicate g (0,0))) c ∧
      (step target c).isNone := by
  have h := a12EL_triple_collect g L
  have he : 2*(g+1) = 2*g+2 := by omega
  rw [he] at h
  obtain ⟨c,hc,hh⟩ := a12CR_triple_positive (2*g) L []
  exact ⟨c,ReachesPlus.trans h hc,hh⟩

theorem a12G_binary_111_zeros_halts (k g : ℕ) (w : List Bool) :
    ∃ c, ReachesPlus target
      (cfg_CR_n_n [(0,0)] (List.replicate (k+1) (0,0) ++
        (a12Binary w ++ ([(1,0),(1,0),(1,0)] ++ List.replicate g (0,0))))) c ∧
      (step target c).isNone := by
  let S := [(1,0),(1,0),(1,0)] ++ List.replicate g (0,0)
  have h := a12G_to_EL k (a12Binary w ++ S)
  obtain ⟨c,hc,hh⟩ := a12EL_prefix_halts S (a12EL_triple_zeros_halts g) w
    (List.replicate (k+2) (0,0) ++ [(1,0)])
  exact ⟨c,ReachesPlus.trans h hc,hh⟩

#print axioms a12CR_triple_positive
#print axioms a12G_binary_111_zeros_halts
