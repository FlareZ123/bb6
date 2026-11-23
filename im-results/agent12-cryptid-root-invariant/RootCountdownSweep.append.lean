/-!
Source-local Lean append draft for the D_n(c) sweep recurrence.
Append inside the pinned #85 source module
M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA, where target,
cfg_*_n_n, bumpPairHead, encLeft/encRight, and execute are in scope.

This file is NOT compiled here. The two sweep proofs are the same source
one-step recurrences sent to Agent 32. The fixed eight-step prefix and
positive-head endpoints are listed in RootCountdownSweep.md and remain to
be composed into the final quantified theorem.
-/

theorem root_countdown_cr_zero_step (L R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_CR_n_n ((0,0) :: L) R)
      (cfg_CR_n_n L (bumpPairHead (bumpPairHead R))) := by
  unfold cfg_CR_n_n
  rw [encRight_mod1 0 0 L, Nat.mod_one 0, encRight_d0_s0 L,
    ← encLeft_cons_one (bumpPairHead R), ← encLeft_cons_one R]
  execute 2

theorem root_countdown_cr_empty_step (R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_CR_n_n [] R)
      (cfg_EL_n_n [(0,0)] (bumpPairHead R)) := by
  unfold cfg_CR_n_n cfg_EL_n_n
  rw [encRight_d0_s0 [], ← encLeft_cons_one R]
  execute 2

theorem root_countdown_el_positive_step (a : ℕ) (L R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_EL_n_n L ((a+1,0) :: R))
      (cfg_DL_0_n L ((a,0) :: R)) := by
  unfold cfg_EL_n_n cfg_DL_0_n
  rw [encLeft_mod1 (a+1) 0 R, Nat.mod_one 0, encLeft_succ a 0 R,
    encLeft_run_s0 a R]
  execute 1

theorem root_countdown_dl_positive_step (a : ℕ) (L R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_DL_0_n L ((a+2,0) :: R))
      (cfg_DR_n_n L ((1,0) :: (a,0) :: R)) := by
  unfold cfg_DL_0_n cfg_DR_n_n
  rw [encLeft_mod1 (a+2) 0 R, Nat.mod_one 0,
    encLeft_succ (a+1) 0 R, encLeft_succ a 0 R,
    encLeft_run_s0 a R, encLeft_d1_s0 ((a,0) :: R),
    encLeft_run_s0 a R]
  execute 4

theorem root_countdown_dr_zero_step (L R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_DR_n_n ((0,0) :: L) ((1,0) :: R))
      (cfg_DR_n_n L ((1,0) :: (0,0) :: R)) := by
  unfold cfg_DR_n_n
  rw [encRight_mod1 0 0 L, Nat.mod_one 0, encRight_d0_s0 L,
    encLeft_mod1 1 0 R, Nat.mod_one 0, encLeft_succ 0 0 R,
    encLeft_run_s0 0 R, encLeft_d1_s0 ((0,0) :: R),
    encLeft_run_s0 0 R]
  execute 4

theorem root_countdown_dr_empty_left_step (R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_DR_n_n [] R)
      (cfg_EL_n_n [(0,0)] R) := by
  unfold cfg_DR_n_n cfg_EL_n_n
  rw [encRight_d0_s0 []]
  execute 1

theorem root_countdown_dl_zero_step (L R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_DL_0_n L ((0,0) :: R))
      (cfg_EL_n_n ((0,0) :: bumpPairHead L) R) := by
  unfold cfg_DL_0_n cfg_EL_n_n
  rw [encLeft_mod1 0 0 R, Nat.mod_one 0, encLeft_d0_s0 R,
    encRight_d0_s0 (bumpPairHead L), ← encRight_cons_one L]
  execute 6

theorem root_countdown_dr_positive_positive_step (a b : ℕ)
    (L R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_DR_n_n ((a+1,0) :: L) ((b+1,0) :: R))
      (cfg_CR_n_n ((a,0) :: L) ((0,0) :: (b,0) :: R)) := by
  unfold cfg_DR_n_n cfg_CR_n_n
  rw [encRight_mod1 (a+1) 0 L, Nat.mod_one 0, encRight_succ a 0 L,
    encRight_run_s0 a L, encLeft_mod1 (b+1) 0 R, Nat.mod_one 0,
    encLeft_succ b 0 R, encLeft_run_s0 b R,
    encLeft_d0_s0 ((b,0) :: R), encLeft_run_s0 b R]
  execute 3

theorem root_countdown_el_zero_step (L R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_EL_n_n L ((0,0) :: R))
      (cfg_EL_n_n ((0,0) :: L) R) := by
  unfold cfg_EL_n_n
  rw [encLeft_mod1 0 0 R, Nat.mod_one 0, encLeft_d0_s0 R,
    encRight_d0_s0 L]
  execute 2

theorem root_countdown_el_zero_sweep (k : ℕ) (L R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_EL_n_n L (List.replicate (k+1) (0,0) ++ R))
      (cfg_EL_n_n (List.replicate (k+1) (0,0) ++ L) R) := by
  induction k generalizing L R with
  | zero =>
      simpa using root_countdown_el_zero_step L R
  | succ k ih =>
      have h1 := root_countdown_el_zero_step L
        (List.replicate (k+1) (0,0) ++ R)
      have h2 := ih ((0,0) :: L) R
      exact ReachesPlus.trans h1
        (by simpa [List.replicate_succ, List.cons_append, List.append_assoc] using h2)

theorem root_countdown_dr_zero_sweep (k : ℕ) (L R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_DR_n_n (List.replicate (k+1) (0,0) ++ L) ((1,0) :: R))
      (cfg_DR_n_n L ((1,0) :: (List.replicate (k+1) (0,0) ++ R))) := by
  induction k generalizing L R with
  | zero =>
      simpa using root_countdown_dr_zero_step L R
  | succ k ih =>
      have h1 := root_countdown_dr_zero_step
        (List.replicate (k+1) (0,0) ++ L) R
      have h2 := ih L ((0,0) :: R)
      exact ReachesPlus.trans h1
        (by simpa [List.replicate_succ, List.cons_append, List.append_assoc] using h2)


/-! Additional helpers for the zero-remainder reset recurrence. -/

theorem root_countdown_cr_one_empty_step (R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_CR_n_n [(1,0)] R)
      (cfg_EL_n_n [(0,0)] ((0,0) :: bumpPairHead (bumpPairHead (bumpPairHead R)))) := by
  unfold cfg_CR_n_n cfg_EL_n_n
  rw [encRight_mod1 1 0 [], Nat.mod_one 0, encRight_d1_s0 [],
    encRight_d0_s0 [],
    encLeft_d0_s0 (bumpPairHead (bumpPairHead (bumpPairHead R))),
    ← encLeft_cons_one (bumpPairHead (bumpPairHead R)),
    ← encLeft_cons_one (bumpPairHead R), ← encLeft_cons_one R]
  execute 6

theorem root_countdown_cr_zero_sweep_singleton (k b : ℕ) (L : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_CR_n_n (List.replicate (k+1) (0,0) ++ L) [(b,0)])
      (cfg_CR_n_n L [(b+2*(k+1),0)]) := by
  induction k generalizing b L with
  | zero =>
      simpa [bumpPairHead] using root_countdown_cr_zero_step L [(b,0)]
  | succ k ih =>
      have h1 := root_countdown_cr_zero_step
        (List.replicate (k+1) (0,0) ++ L) [(b,0)]
      have h1' : ReachesPlus target
          (cfg_CR_n_n (List.replicate (k+1) (0,0) ++ L) [(b,0)])
          (cfg_CR_n_n (List.replicate (k+1) (0,0) ++ L) [(b+2,0)]) := by
        simpa [bumpPairHead] using h1
      have h2 := ih (b+2) L
      have hval : b+2+2*(k+1) = b+2*(k+2) := by omega
      have h2' : ReachesPlus target
          (cfg_CR_n_n (List.replicate (k+1) (0,0) ++ L) [(b+2,0)])
          (cfg_CR_n_n L [(b+2*(k+2),0)]) := by
        simpa [hval] using h2
      exact ReachesPlus.trans h1' h2'


theorem root_countdown_el_empty_step (L : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_EL_n_n L [])
      (cfg_CR_n_n L [(0,0)]) := by
  unfold cfg_EL_n_n cfg_CR_n_n
  rw [encLeft_d0_s0 []]
  execute 1

theorem root_countdown_prefix (n c : ℕ) :
    ReachesPlus target
      (cfg_CR_n_n [(0,0)]
        (List.replicate (4*n+5) (0,0) ++ [(c,0)]))
      (cfg_EL_n_n [(0,0),(1,0)]
        (List.replicate (4*n+6) (0,0) ++ [(c,0)])) := by
  let tail : List (ℕ × ℕ) := List.replicate (4*n+4) (0,0) ++ [(c,0)]
  have h1 :
      ReachesPlus target
        (cfg_CR_n_n [(0,0)]
          (List.replicate (4*n+5) (0,0) ++ [(c,0)]))
        (cfg_CR_n_n [] ((2,0) :: tail)) := by
    simpa [tail, bumpPairHead, List.replicate_succ] using
      (root_countdown_cr_zero_step [] (List.replicate (4*n+5) (0,0) ++ [(c,0)]))
  have h2 :
      ReachesPlus target
        (cfg_CR_n_n [] ((2,0) :: tail))
        (cfg_EL_n_n [(0,0)] ((3,0) :: tail)) := by
    simpa [bumpPairHead] using root_countdown_cr_empty_step ((2,0) :: tail)
  have h3 :=
    root_countdown_el_positive_step 2 [(0,0)] tail
  have h4 :=
    root_countdown_dl_positive_step 0 [(0,0)] tail
  have h5 :=
    root_countdown_dr_zero_step [] ((0,0) :: tail)
  have h6 :=
    root_countdown_dr_empty_left_step
      ((1,0) :: (0,0) :: (0,0) :: tail)
  have h7 :=
    root_countdown_el_positive_step 0 [(0,0)] ((0,0) :: (0,0) :: tail)
  have h8 :
      ReachesPlus target
        (cfg_DL_0_n [(0,0)] ((0,0) :: (0,0) :: (0,0) :: tail))
        (cfg_EL_n_n [(0,0),(1,0)] ((0,0) :: (0,0) :: tail)) := by
    simpa [bumpPairHead] using
      (root_countdown_dl_zero_step [(0,0)] ((0,0) :: (0,0) :: tail))
  simpa [tail, List.replicate_succ, List.cons_append, List.append_assoc] using
    (ReachesPlus.trans h1
      (ReachesPlus.trans h2
        (ReachesPlus.trans h3
          (ReachesPlus.trans h4
            (ReachesPlus.trans h5
              (ReachesPlus.trans h6
                (ReachesPlus.trans h7 h8)))))))


theorem root_countdown_zero_reset_tail (n : ℕ) :
    ReachesPlus target
      (cfg_EL_n_n [(0,0)] [(0,0), (8*n+19,0)])
      (cfg_CR_n_n [(0,0)]
        (List.replicate 5 (0,0) ++ [(8*n+13,0)])) := by
  have h1 := root_countdown_el_zero_step [(0,0)] [(8*n+19,0)]
  have h2 := root_countdown_el_positive_step (8*n+18)
    [(0,0),(0,0)] []
  have h3 := root_countdown_dl_positive_step (8*n+16)
    [(0,0),(0,0)] []
  have h4 := root_countdown_dr_zero_sweep 1 []
    [(8*n+16,0)]
  have h5 := root_countdown_dr_empty_left_step
    [(1,0),(0,0),(0,0),(8*n+16,0)]
  have h6 := root_countdown_el_positive_step 0 [(0,0)]
    [(0,0),(0,0),(8*n+16,0)]
  have h7 := root_countdown_dl_zero_step [(0,0)]
    [(0,0),(0,0),(8*n+16,0)]
  have h8 := root_countdown_el_zero_sweep 1 [(0,0),(1,0)]
    [(8*n+16,0)]
  have h9 := root_countdown_el_positive_step (8*n+15)
    [(0,0),(0,0),(0,0),(1,0)] []
  have h10 := root_countdown_dl_positive_step (8*n+13)
    [(0,0),(0,0),(0,0),(1,0)] []
  have h11 := root_countdown_dr_zero_sweep 2 [(1,0)]
    [(8*n+13,0)]
  have h12 := root_countdown_dr_positive_positive_step 0 0 []
    (List.replicate 3 (0,0) ++ [(8*n+13,0)])
  simpa [List.replicate_succ, List.cons_append, List.append_assoc] using
    (ReachesPlus.trans h1
      (ReachesPlus.trans h2
        (ReachesPlus.trans h3
          (ReachesPlus.trans h4
            (ReachesPlus.trans h5
              (ReachesPlus.trans h6
                (ReachesPlus.trans h7
                  (ReachesPlus.trans h8
                    (ReachesPlus.trans h9
                      (ReachesPlus.trans h10
                        (ReachesPlus.trans h11 h12)))))))))))



theorem root_countdown_zero_reset (n : ℕ) :
    ReachesPlus target
      (cfg_CR_n_n [(0,0)] (List.replicate (4*n+6) (0,0)))
      (cfg_CR_n_n [(0,0)]
        (List.replicate 5 (0,0) ++ [(8*n+13,0)])) := by
  have h1 := root_countdown_prefix n 0
  have h2 := root_countdown_el_zero_sweep (4*n+6) [(0,0),(1,0)] []
  have h2' : ReachesPlus target
      (cfg_EL_n_n [(0,0),(1,0)]
        (List.replicate (4*n+6) (0,0) ++ [(0,0)]))
      (cfg_EL_n_n (List.replicate (4*n+7) (0,0) ++ [(0,0),(1,0)]) []) := by
    simpa [List.replicate_succ, List.cons_append, List.append_assoc] using h2
  have h3 := root_countdown_el_empty_step
    (List.replicate (4*n+7) (0,0) ++ [(0,0),(1,0)])
  have h4 := root_countdown_cr_zero_sweep_singleton (4*n+7) 0 [(1,0)]
  have h4' : ReachesPlus target
      (cfg_CR_n_n (List.replicate (4*n+7) (0,0) ++ [(0,0),(1,0)]) [(0,0)])
      (cfg_CR_n_n [(1,0)] [(8*n+16,0)]) := by
    simpa [List.replicate_succ, List.cons_append, List.append_assoc] using h4
  have h5 := root_countdown_cr_one_empty_step [(8*n+16,0)]
  have h6 := root_countdown_zero_reset_tail n
  have hcount : 2*(4*n+8) = 8*n+16 := by omega
  simpa [List.replicate_succ, List.cons_append, List.append_assoc,
    bumpPairHead, hcount] using
    (ReachesPlus.trans h1
      (ReachesPlus.trans h2'
        (ReachesPlus.trans h3
          (ReachesPlus.trans h4'
            (ReachesPlus.trans h5 h6)))))


theorem root_countdown_step (n c : ℕ) (hc : 3 ≤ c) :
    ReachesPlus target
      (cfg_CR_n_n [(0,0)]
        (List.replicate (4*n+5) (0,0) ++ [(c,0)]))
      (cfg_CR_n_n [(0,0)]
        (List.replicate (4*(n+1)+5) (0,0) ++ [(c-3,0)])) := by
  have h1 := root_countdown_prefix n c
  have h2 := root_countdown_el_zero_sweep (4*n+5)
    [(0,0),(1,0)] [(c,0)]
  have h2' : ReachesPlus target
      (cfg_EL_n_n [(0,0),(1,0)]
        (List.replicate (4*n+6) (0,0) ++ [(c,0)]))
      (cfg_EL_n_n (List.replicate (4*n+7) (0,0) ++ [(1,0)]) [(c,0)]) := by
    simpa [List.replicate_succ, List.cons_append, List.append_assoc] using h2
  have hc1 : c-1+1 = c := by omega
  have hc2 : c-3+2 = c-1 := by omega
  have h3 := root_countdown_el_positive_step (c-1)
    (List.replicate (4*n+7) (0,0) ++ [(1,0)]) []
  have h3' : ReachesPlus target
      (cfg_EL_n_n (List.replicate (4*n+7) (0,0) ++ [(1,0)]) [(c,0)])
      (cfg_DL_0_n (List.replicate (4*n+7) (0,0) ++ [(1,0)]) [(c-1,0)]) := by
    simpa [hc1] using h3
  have h4 := root_countdown_dl_positive_step (c-3)
    (List.replicate (4*n+7) (0,0) ++ [(1,0)]) []
  have h4' : ReachesPlus target
      (cfg_DL_0_n (List.replicate (4*n+7) (0,0) ++ [(1,0)]) [(c-1,0)])
      (cfg_DR_n_n (List.replicate (4*n+7) (0,0) ++ [(1,0)]) [(1,0),(c-3,0)]) := by
    simpa [hc2] using h4
  have h5 := root_countdown_dr_zero_sweep (4*n+6) [(1,0)]
    [(c-3,0)]
  have h6 := root_countdown_dr_positive_positive_step 0 0 []
    (List.replicate (4*n+7) (0,0) ++ [(c-3,0)])
  have hn : 4*(n+1)+5 = 4*n+9 := by omega
  simpa [List.replicate_succ, List.cons_append, List.append_assoc,
    hc1, hc2, hn] using
    (ReachesPlus.trans h1
      (ReachesPlus.trans h2'
        (ReachesPlus.trans h3'
          (ReachesPlus.trans h4'
            (ReachesPlus.trans h5 h6)))))


theorem root_seed_to_D0_3 :
    ReachesPlus target
      (cfg_DR_n_n [(0,0),(0,0)] [(1,0)])
      (cfg_CR_n_n [(0,0)]
        (List.replicate 5 (0,0) ++ [(3,0)])) := by
  have h1 := root_countdown_dr_zero_step [(0,0)] []
  have h2 := root_countdown_dr_zero_step [] [(0,0)]
  have h3 := root_countdown_dr_empty_left_step
    [(1,0),(0,0),(0,0)]
  have h4 := root_countdown_el_positive_step 0 [(0,0)]
    [(0,0),(0,0)]
  have h5 := root_countdown_dl_zero_step [(0,0)]
    [(0,0),(0,0)]
  have h6 := root_countdown_el_zero_sweep 1 [(0,0),(1,0)] []
  have h7 := root_countdown_el_empty_step
    [(0,0),(0,0),(0,0),(1,0)]
  have h8 := root_countdown_cr_zero_sweep_singleton 2 0 [(1,0)]
  have h9 := root_countdown_cr_one_empty_step [(6,0)]
  have h10 := root_countdown_el_zero_step [(0,0)] [(9,0)]
  have h11 := root_countdown_el_positive_step 8 [(0,0),(0,0)] []
  have h12 := root_countdown_dl_positive_step 6 [(0,0),(0,0)] []
  have h13 := root_countdown_dr_zero_sweep 1 [] [(6,0)]
  have h14 := root_countdown_dr_empty_left_step
    [(1,0),(0,0),(0,0),(6,0)]
  have h15 := root_countdown_el_positive_step 0 [(0,0)]
    [(0,0),(0,0),(6,0)]
  have h16 := root_countdown_dl_zero_step [(0,0)]
    [(0,0),(0,0),(6,0)]
  have h17 := root_countdown_el_zero_sweep 1 [(0,0),(1,0)] [(6,0)]
  have h18 := root_countdown_el_positive_step 5
    [(0,0),(0,0),(0,0),(1,0)] []
  have h19 := root_countdown_dl_positive_step 3
    [(0,0),(0,0),(0,0),(1,0)] []
  have h20 := root_countdown_dr_zero_sweep 2 [(1,0)] [(3,0)]
  have h21 := root_countdown_dr_positive_positive_step 0 0 []
    (List.replicate 3 (0,0) ++ [(3,0)])
  simpa [List.replicate_succ, List.cons_append, List.append_assoc,
    bumpPairHead] using
    (ReachesPlus.trans h1
      (ReachesPlus.trans h2
        (ReachesPlus.trans h3
          (ReachesPlus.trans h4
            (ReachesPlus.trans h5
              (ReachesPlus.trans h6
                (ReachesPlus.trans h7
                  (ReachesPlus.trans h8
                    (ReachesPlus.trans h9
                      (ReachesPlus.trans h10
                        (ReachesPlus.trans h11
                          (ReachesPlus.trans h12
                            (ReachesPlus.trans h13
                              (ReachesPlus.trans h14
                                (ReachesPlus.trans h15
                                  (ReachesPlus.trans h16
                                    (ReachesPlus.trans h17
                                      (ReachesPlus.trans h18
                                        (ReachesPlus.trans h19
                                          (ReachesPlus.trans h20 h21))))))))))))))))))))


theorem root_countdown_iter_succ (m n c : ℕ)
    (hc : 3*(m+1) ≤ c) :
    ReachesPlus target
      (cfg_CR_n_n [(0,0)]
        (List.replicate (4*n+5) (0,0) ++ [(c,0)]))
      (cfg_CR_n_n [(0,0)]
        (List.replicate (4*(n+(m+1))+5) (0,0) ++ [(c-3*(m+1),0)])) := by
  induction m generalizing n c with
  | zero =>
      simpa using root_countdown_step n c (by omega)
  | succ m ih =>
      have hfirst := root_countdown_step n c (by omega)
      have hrest := ih (n+1) (c-3) (by omega)
      have hidx : (n+1)+(m+1) = n+(m+2) := by omega
      have hval : c-3-3*(m+1) = c-3*(m+2) := by omega
      simpa [hidx, hval] using ReachesPlus.trans hfirst hrest

theorem root_chain_to_D65_2 :
    ReachesPlus target
      (cfg_DR_n_n [(0,0),(0,0)] [(1,0)])
      (cfg_CR_n_n [(0,0)]
        (List.replicate (4*65+5) (0,0) ++ [(2,0)])) := by
  have h0 := root_seed_to_D0_3
  have h1 := root_countdown_iter_succ 0 0 3 (by omega)
  have h1' : ReachesPlus target
      (cfg_CR_n_n [(0,0)] (List.replicate 5 (0,0) ++ [(3,0)]))
      (cfg_CR_n_n [(0,0)] (List.replicate 10 (0,0))) := by
    simpa [List.replicate_succ] using h1
  have h2 := root_countdown_zero_reset 1
  have h3 := root_countdown_iter_succ 6 0 21 (by omega)
  have h3' : ReachesPlus target
      (cfg_CR_n_n [(0,0)] (List.replicate 5 (0,0) ++ [(21,0)]))
      (cfg_CR_n_n [(0,0)] (List.replicate 34 (0,0))) := by
    simpa [List.replicate_succ] using h3
  have h4 := root_countdown_zero_reset 7
  have h5 := root_countdown_iter_succ 22 0 69 (by omega)
  have h5' : ReachesPlus target
      (cfg_CR_n_n [(0,0)] (List.replicate 5 (0,0) ++ [(69,0)]))
      (cfg_CR_n_n [(0,0)] (List.replicate 98 (0,0))) := by
    simpa [List.replicate_succ] using h5
  have h6 := root_countdown_zero_reset 23
  have h7 := root_countdown_iter_succ 64 0 197 (by omega)
  exact ReachesPlus.trans h0
    (ReachesPlus.trans h1'
      (ReachesPlus.trans h2
        (ReachesPlus.trans h3'
          (ReachesPlus.trans h4
            (ReachesPlus.trans h5'
              (ReachesPlus.trans h6 h7))))))


theorem root_countdown_general_tail (x : ℕ) (hx : 6 ≤ x) :
    ReachesPlus target
      (cfg_EL_n_n [(0,0)] [(0,0),(x,0)])
      (cfg_CR_n_n [(0,0)]
        (List.replicate 5 (0,0) ++ [(x-6,0)])) := by
  have h1 := root_countdown_el_zero_step [(0,0)] [(x,0)]
  have hx1 : x-1+1 = x := by omega
  have hx2 : x-3+2 = x-1 := by omega
  have hx3 : x-4+1 = x-3 := by omega
  have hx4 : x-6+2 = x-4 := by omega
  have h2 := root_countdown_el_positive_step (x-1)
    [(0,0),(0,0)] []
  have h2' : ReachesPlus target
      (cfg_EL_n_n [(0,0),(0,0)] [(x,0)])
      (cfg_DL_0_n [(0,0),(0,0)] [(x-1,0)]) := by
    simpa [hx1] using h2
  have h3 := root_countdown_dl_positive_step (x-3)
    [(0,0),(0,0)] []
  have h3' : ReachesPlus target
      (cfg_DL_0_n [(0,0),(0,0)] [(x-1,0)])
      (cfg_DR_n_n [(0,0),(0,0)] [(1,0),(x-3,0)]) := by
    simpa [hx2] using h3
  have h4 := root_countdown_dr_zero_sweep 1 [] [(x-3,0)]
  have h5 := root_countdown_dr_empty_left_step
    [(1,0),(0,0),(0,0),(x-3,0)]
  have h6 := root_countdown_el_positive_step 0 [(0,0)]
    [(0,0),(0,0),(x-3,0)]
  have h7 := root_countdown_dl_zero_step [(0,0)]
    [(0,0),(0,0),(x-3,0)]
  have h8 := root_countdown_el_zero_sweep 1 [(0,0),(1,0)]
    [(x-3,0)]
  have h9 := root_countdown_el_positive_step (x-4)
    [(0,0),(0,0),(0,0),(1,0)] []
  have h9' : ReachesPlus target
      (cfg_EL_n_n [(0,0),(0,0),(0,0),(1,0)] [(x-3,0)])
      (cfg_DL_0_n [(0,0),(0,0),(0,0),(1,0)] [(x-4,0)]) := by
    simpa [hx3] using h9
  have h10 := root_countdown_dl_positive_step (x-6)
    [(0,0),(0,0),(0,0),(1,0)] []
  have h10' : ReachesPlus target
      (cfg_DL_0_n [(0,0),(0,0),(0,0),(1,0)] [(x-4,0)])
      (cfg_DR_n_n [(0,0),(0,0),(0,0),(1,0)] [(1,0),(x-6,0)]) := by
    simpa [hx4] using h10
  have h11 := root_countdown_dr_zero_sweep 2 [(1,0)]
    [(x-6,0)]
  have h12 := root_countdown_dr_positive_positive_step 0 0 []
    (List.replicate 3 (0,0) ++ [(x-6,0)])
  simpa [List.replicate_succ, List.cons_append, List.append_assoc,
    bumpPairHead, hx1, hx2, hx3, hx4] using
    (ReachesPlus.trans h1
      (ReachesPlus.trans h2'
        (ReachesPlus.trans h3'
          (ReachesPlus.trans h4
            (ReachesPlus.trans h5
              (ReachesPlus.trans h6
                (ReachesPlus.trans h7
                  (ReachesPlus.trans h8
                    (ReachesPlus.trans h9'
                      (ReachesPlus.trans h10'
                        (ReachesPlus.trans h11 h12)))))))))))
