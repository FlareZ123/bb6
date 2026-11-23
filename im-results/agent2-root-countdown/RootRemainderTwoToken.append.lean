/-!
Source-local Lean append draft for the #85 remainder-two reset.

Append this fragment to the pinned
M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA source module, after
RootCountdownSweep.append.lean. It uses private source lemmas
tok_DR_zero, tok_DR_1_nil_28, tok_EL_1, and tok_EL_exit_zero.
This file is NOT compiled and is not a standalone Lean module.

For m=4n+7, the DL right-head-one token route is:
  tok_DR [2,0] R3 (0^m ++ [1])
    -- tok_DR_zero^m -->
  tok_DR [2,1^m,0] R3 [1]
    -- tok_DR_1_nil_28 -->
  tok_EL [1^(m+1),0] R3 [0,0,0,1]
    -- tok_EL_1^(m+1) -->
  tok_EL [0] R3 (0^(m+4) ++ [1])
    -- tok_EL_exit_zero -->
  CR(0^(m+4) ++ [1], bumpPairHead R3).

For R3=[], bumpPairHead []=[0], so the endpoint is
CR(0^(4n+11) ++ [1], [0]). The token subroutine costs 6m+31 raw
steps; including the four-step DL entry gives 6m+35=24n+77.
The full D_n(2) reset costs 8n+44 outer successors and 40n+186
primitive steps, ending at D_0(8n+19).

This fragment depends on the helper declarations in
RootCountdownSweep.append.lean and has not passed local Lean preflight.
-/


/-
The upstream root_countdown_prefix draft has an off-by-one endpoint
mismatch in its DR-zero / DR-empty-left composition. This local
suffix-preserving version uses the corrected source-clause arguments.
Agent 24's audit identifies the same correction in the shared draft.
-/
theorem root_countdown_prefix_with_tail_fixed (n c : ℕ)
    (T : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_CR_n_n [(0,0)]
        (List.replicate (4*n+5) (0,0) ++ [(c,0)] ++ T))
      (cfg_EL_n_n [(0,0),(1,0)]
        (List.replicate (4*n+6) (0,0) ++ [(c,0)] ++ T)) := by
  let tail : List (ℕ × ℕ) :=
    List.replicate (4*n+4) (0,0) ++ [(c,0)] ++ T
  have h1 :
      ReachesPlus target
        (cfg_CR_n_n [(0,0)]
          (List.replicate (4*n+5) (0,0) ++ [(c,0)] ++ T))
        (cfg_CR_n_n [] ((2,0) :: tail)) := by
    simpa [tail, bumpPairHead, List.replicate_succ,
      List.cons_append, List.append_assoc] using
      (root_countdown_cr_zero_step []
        (List.replicate (4*n+5) (0,0) ++ [(c,0)] ++ T))
  have h2 :
      ReachesPlus target
        (cfg_CR_n_n [] ((2,0) :: tail))
        (cfg_EL_n_n [(0,0)] ((3,0) :: tail)) := by
    simpa [bumpPairHead] using
      (root_countdown_cr_empty_step ((2,0) :: tail))
  have h3 := root_countdown_el_positive_step 2 [(0,0)] tail
  have h4 := root_countdown_dl_positive_step 0 [(0,0)] tail
  have h5 := root_countdown_dr_zero_step [] ((0,0) :: tail)
  have h6 := root_countdown_dr_empty_left_step
    ((1,0) :: (0,0) :: (0,0) :: tail)
  have h7 := root_countdown_el_positive_step 0 [(0,0)]
    ((0,0) :: (0,0) :: tail)
  have h8 :
      ReachesPlus target
        (cfg_DL_0_n [(0,0)]
          ((0,0) :: (0,0) :: (0,0) :: tail))
        (cfg_EL_n_n [(0,0),(1,0)]
          ((0,0) :: (0,0) :: tail)) := by
    simpa [bumpPairHead] using
      (root_countdown_dl_zero_step [(0,0)]
        ((0,0) :: (0,0) :: tail))
  simpa [tail, List.replicate_succ, List.cons_append,
    List.append_assoc] using
    (ReachesPlus.trans h1
      (ReachesPlus.trans h2
        (ReachesPlus.trans h3
          (ReachesPlus.trans h4
            (ReachesPlus.trans h5
              (ReachesPlus.trans h6
                (ReachesPlus.trans h7 h8)))))))


private theorem root_d2_tok_dr_zero_sweep (k : ℕ) (K1 : List ℕ)
    (R3 : List (ℕ × ℕ)) (L : List ℕ) :
    ReachesPlus target
      (tok_DR (2 :: K1) R3 (List.replicate (k+1) 0 ++ L))
      (tok_DR (2 :: List.replicate (k+1) 1 ++ K1) R3 L) := by
  induction k generalizing K1 L with
  | zero =>
      simpa [List.replicate_succ, List.cons_append] using
        (tok_DR_zero K1 R3 L)
  | succ k ih =>
      have h1 :
          ReachesPlus target
            (tok_DR (2 :: K1) R3
              (List.replicate (k+2) 0 ++ L))
            (tok_DR (2 :: 1 :: K1) R3
              (List.replicate (k+1) 0 ++ L)) := by
        simpa [List.replicate_succ, List.cons_append] using
          (tok_DR_zero K1 R3 (List.replicate (k+1) 0 ++ L))
      have h2 := ih (1 :: K1) L
      exact ReachesPlus.trans h1 (by
        simpa [List.replicate_succ, List.cons_append, List.append_assoc] using h2)


private theorem root_d2_tok_el_one_sweep (k : ℕ) (K1 : List ℕ)
    (R3 : List (ℕ × ℕ)) (L : List ℕ) :
    ReachesPlus target
      (tok_EL (List.replicate (k+1) 1 ++ K1) R3 L)
      (tok_EL K1 R3 (List.replicate (k+1) 0 ++ L)) := by
  induction k generalizing K1 L with
  | zero =>
      simpa [List.replicate_succ, List.cons_append] using
        (tok_EL_1 K1 R3 L)
  | succ k ih =>
      have h1 :
          ReachesPlus target
            (tok_EL (List.replicate (k+2) 1 ++ K1) R3 L)
            (tok_EL (List.replicate (k+1) 1 ++ K1) R3 (0 :: L)) := by
        simpa [List.replicate_succ, List.cons_append] using
          (tok_EL_1 (List.replicate (k+1) 1 ++ K1) R3 L)
      have h2 := ih K1 (0 :: L)
      exact ReachesPlus.trans h1 (by
        simpa [List.replicate_succ, List.cons_append, List.append_assoc] using h2)


private theorem root_d2_tok_dr_z1 (k : ℕ) (R3 : List (ℕ × ℕ)) :
    ReachesPlus target
      (tok_DR [2,0] R3 (List.replicate (k+1) 0 ++ [1]))
      (cfg_CR_n_n
        ((List.replicate (k+5) 0 ++ [1]).map (fun x => (x,0)))
        (bumpPairHead R3)) := by
  have h1 := root_d2_tok_dr_zero_sweep k [0] R3 [1]
  have h2 :
      ReachesPlus target
        (tok_DR (2 :: List.replicate (k+1) 1 ++ [0]) R3 [1])
        (tok_EL (List.replicate (k+2) 1 ++ [0]) R3 [0,0,0,1]) := by
    simpa [List.replicate_succ, List.cons_append, List.append_assoc] using
      (tok_DR_1_nil_28 (List.replicate (k+1) 1 ++ [0]) R3)
  have h3 :
      ReachesPlus target
        (tok_EL (List.replicate (k+2) 1 ++ [0]) R3 [0,0,0,1])
        (tok_EL [0] R3 (List.replicate (k+5) 0 ++ [1])) := by
    simpa [List.replicate_succ, List.cons_append, List.append_assoc] using
      (root_d2_tok_el_one_sweep (k+1) [0] R3 [0,0,0,1])
  have h4 := tok_EL_exit_zero R3 (List.replicate (k+5) 0 ++ [1])
  exact ReachesPlus.trans h1 (ReachesPlus.trans h2 (ReachesPlus.trans h3 h4))


private theorem root_d2_dl_one_z1 (k : ℕ) :
    ReachesPlus target
      (cfg_DL_0_n (List.replicate (k+1) (0,0) ++ [(1,0)]) [(1,0)])
      (cfg_CR_n_n (List.replicate (k+5) (0,0) ++ [(1,0)]) [(0,0)]) := by
  have h1 :
      ReachesPlus target
        (cfg_DL_0_n (List.replicate (k+1) (0,0) ++ [(1,0)]) [(1,0)])
        (tok_DR [2,0] [] (List.replicate (k+1) 0 ++ [1])) := by
    unfold cfg_DL_0_n tok_DR
    rw [encLeft_mod1 1 0 [], Nat.mod_one 0, encLeft_d1_s0 [],
      encRight_eq_nat (List.replicate (k+1) (0,0) ++ [(1,0)]),
      encTokens_succ, encTokens_succ, encTokens_zero, encTokens_zero,
      encTokens_nil]
    texecute 4
  have h2 := root_d2_tok_dr_z1 k []
  simpa [bumpPairHead, List.map_replicate, List.map_append] using
    (ReachesPlus.trans h1 h2)


theorem root_countdown_two_reset (n : ℕ) :
    ReachesPlus target
      (cfg_CR_n_n [(0,0)]
        (List.replicate (4*n+5) (0,0) ++ [(2,0)]))
      (cfg_CR_n_n [(0,0)]
        (List.replicate 5 (0,0) ++ [(8*n+19,0)])) := by
  have h1 := root_countdown_prefix_with_tail_fixed n 2 []
  have h2 := root_countdown_el_zero_sweep (4*n+5)
    [(0,0),(1,0)] [(2,0)]
  have h2' : ReachesPlus target
      (cfg_EL_n_n [(0,0),(1,0)]
        (List.replicate (4*n+6) (0,0) ++ [(2,0)]))
      (cfg_EL_n_n (List.replicate (4*n+7) (0,0) ++ [(1,0)]) [(2,0)]) := by
    simpa [List.replicate_succ, List.cons_append, List.append_assoc] using h2
  have h3 := root_countdown_el_positive_step 1
    (List.replicate (4*n+7) (0,0) ++ [(1,0)]) []
  have h4 := root_d2_dl_one_z1 (4*n+6)
  have h5 := root_countdown_cr_zero_sweep_singleton (4*n+10) 0 [(1,0)]
  have h6 := root_countdown_cr_one_empty_step [(8*n+22,0)]
  have h7 := root_countdown_general_tail (8*n+25) (by omega)
  have hcount : 2*(4*n+11) = 8*n+22 := by omega
  have h4' :
      ReachesPlus target
        (cfg_DL_0_n (List.replicate (4*n+7) (0,0) ++ [(1,0)]) [(1,0)])
        (cfg_CR_n_n (List.replicate (4*n+11) (0,0) ++ [(1,0)]) [(0,0)]) := by
    simpa [List.replicate_succ, List.cons_append, List.append_assoc,
      bumpPairHead, List.map_replicate, List.map_append] using
      (root_d2_dl_one_z1 (4*n+6))
  have h5' :
      ReachesPlus target
        (cfg_CR_n_n (List.replicate (4*n+11) (0,0) ++ [(1,0)]) [(0,0)])
        (cfg_CR_n_n [(1,0)] [(8*n+22,0)]) := by
    simpa [List.replicate_succ, List.cons_append, List.append_assoc, hcount] using h5
  have h6' :
      ReachesPlus target
        (cfg_CR_n_n [(1,0)] [(8*n+22,0)])
        (cfg_EL_n_n [(0,0)] [(0,0),(8*n+25,0)]) := by
    simpa [bumpPairHead] using h6
  have hchain :=
    ReachesPlus.trans h1
      (ReachesPlus.trans h2'
        (ReachesPlus.trans h3
          (ReachesPlus.trans h4'
            (ReachesPlus.trans h5' (ReachesPlus.trans h6' h7)))))
  simpa [List.replicate_succ, List.cons_append, List.append_assoc] using hchain


/-!
## Suffix-preserving CR sweeps and the remainder-one resets

The generic tail below is parameterized by the untouched stack suffix.  The
remainder-one reset with suffix [5] is deliberately stated with the exact
source-produced suffix [0,0,0,2]; it must not be shortened to [0,0,2].
-/

private theorem root_countdown_cr_one_zero_step (L : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_CR_n_n ((1,0)::(0,0)::L) [(2,0)])
      (cfg_CR_n_n L [(0,0),(5,0)]) := by
  unfold cfg_CR_n_n
  rw [encLeft_run_s0 2 [], encRight_d1_s0 ((0,0)::L), encRight_d0_s0 L,
    encLeft_d0_s0 [(5,0)], encLeft_run_s0 5 []]
  execute 5

theorem root_countdown_cr_zero_sweep_pair (k b : ℕ)
    (L R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_CR_n_n (List.replicate (k+1) (0,0) ++ L) ((b,0)::R))
      (cfg_CR_n_n L ((b+2*(k+1),0)::R)) := by
  induction k generalizing b L R with
  | zero =>
      simpa [bumpPairHead] using
        (root_countdown_cr_zero_step L ((b,0)::R))
  | succ k ih =>
      have h1 := root_countdown_cr_zero_step
        (List.replicate (k+1) (0,0) ++ L) ((b,0)::R)
      have h1' : ReachesPlus target
          (cfg_CR_n_n (List.replicate (k+2) (0,0) ++ L) ((b,0)::R))
          (cfg_CR_n_n (List.replicate (k+1) (0,0) ++ L) ((b+2,0)::R)) := by
        simpa [List.replicate_succ, List.cons_append, List.append_assoc,
          bumpPairHead] using h1
      have h2 := ih (b+2) L R
      have h2' : ReachesPlus target
          (cfg_CR_n_n (List.replicate (k+1) (0,0) ++ L) ((b+2,0)::R))
          (cfg_CR_n_n L ((b+2*(k+2),0)::R)) := by
        have hval : b+2+2*(k+1) = b+2*(k+2) := by omega
        simpa [hval] using h2
      exact ReachesPlus.trans h1' h2'

theorem root_countdown_general_tail_with_suffix (x : ℕ)
    (T : List (ℕ × ℕ)) (hx : 6 ≤ x) :
    ReachesPlus target
      (cfg_EL_n_n [(0,0)] ([(0,0),(x,0)] ++ T))
      (cfg_CR_n_n [(0,0)]
        (List.replicate 5 (0,0) ++ [(x-6,0)] ++ T)) := by
  have hx1 : x-1+1 = x := by omega
  have hx2 : x-3+2 = x-1 := by omega
  have hx3 : x-4+1 = x-3 := by omega
  have hx4 : x-6+2 = x-4 := by omega
  have h1 := root_countdown_el_zero_step [(0,0)] ([(x,0)] ++ T)
  have h2 := root_countdown_el_positive_step (x-1) [(0,0),(0,0)] T
  have h2' : ReachesPlus target
      (cfg_EL_n_n [(0,0),(0,0)] ([(x,0)] ++ T))
      (cfg_DL_0_n [(0,0),(0,0)] ([(x-1,0)] ++ T)) := by
    simpa [hx1] using h2
  have h3 := root_countdown_dl_positive_step (x-3) [(0,0),(0,0)] T
  have h3' : ReachesPlus target
      (cfg_DL_0_n [(0,0),(0,0)] ([(x-1,0)] ++ T))
      (cfg_DR_n_n [(0,0),(0,0)] ([(1,0),(x-3,0)] ++ T)) := by
    simpa [hx2] using h3
  have h4 := root_countdown_dr_zero_sweep 1 [] ([(x-3,0)] ++ T)
  have h5 := root_countdown_dr_empty_left_step
    ([(1,0),(0,0),(0,0),(x-3,0)] ++ T)
  have h6 := root_countdown_el_positive_step 0 [(0,0)]
    ([(0,0),(0,0),(x-3,0)] ++ T)
  have h7 := root_countdown_dl_zero_step [(0,0)]
    ([(0,0),(0,0),(x-3,0)] ++ T)
  have h8 := root_countdown_el_zero_sweep 1 [(0,0),(1,0)] ([(x-3,0)] ++ T)
  have h9 := root_countdown_el_positive_step (x-4)
    [(0,0),(0,0),(0,0),(1,0)] T
  have h9' : ReachesPlus target
      (cfg_EL_n_n [(0,0),(0,0),(0,0),(1,0)] ([(x-3,0)] ++ T))
      (cfg_DL_0_n [(0,0),(0,0),(0,0),(1,0)] ([(x-4,0)] ++ T)) := by
    simpa [hx3] using h9
  have h10 := root_countdown_dl_positive_step (x-6)
    [(0,0),(0,0),(0,0),(1,0)] T
  have h10' : ReachesPlus target
      (cfg_DL_0_n [(0,0),(0,0),(0,0),(1,0)] ([(x-4,0)] ++ T))
      (cfg_DR_n_n [(0,0),(0,0),(0,0),(1,0)] ([(1,0),(x-6,0)] ++ T)) := by
    simpa [hx4] using h10
  have h11 := root_countdown_dr_zero_sweep 2 [(1,0)] ([(x-6,0)] ++ T)
  have h12 := root_countdown_dr_positive_positive_step 0 0 []
    (List.replicate 3 (0,0) ++ [(x-6,0)] ++ T)
  exact ReachesPlus.trans h1
    (ReachesPlus.trans h2'
      (ReachesPlus.trans h3'
        (ReachesPlus.trans h4
          (ReachesPlus.trans h5
            (ReachesPlus.trans h6
              (ReachesPlus.trans h7
                (ReachesPlus.trans h8
                  (ReachesPlus.trans h9'
                    (ReachesPlus.trans h10'
                      (ReachesPlus.trans h11 h12))))))))))

theorem root_countdown_one_reset (n : ℕ) :
    ReachesPlus target
      (cfg_CR_n_n [(0,0)]
        (List.replicate (4*n+5) (0,0) ++ [(1,0)]))
      (cfg_CR_n_n [(0,0)]
        (List.replicate 5 (0,0) ++ [(8*n+7,0),(5,0)])) := by
  have h1 := root_countdown_prefix_with_tail_fixed n 1 []
  have h2 := root_countdown_el_zero_sweep (4*n+5) [(0,0),(1,0)] [(1,0)]
  have h2' : ReachesPlus target
      (cfg_EL_n_n [(0,0),(1,0)]
        (List.replicate (4*n+6) (0,0) ++ [(1,0)]))
      (cfg_EL_n_n (List.replicate (4*n+7) (0,0) ++ [(1,0)]) [(1,0)]) := by
    simpa [List.replicate_succ, List.cons_append, List.append_assoc] using h2
  have h3 := root_countdown_el_positive_step 0
    (List.replicate (4*n+7) (0,0) ++ [(1,0)]) []
  have h4 := root_countdown_dl_zero_step
    (List.replicate (4*n+7) (0,0) ++ [(1,0)]) []
  have h5 := root_countdown_el_empty_step
    ([(0,0),(1,0)] ++ List.replicate (4*n+6) (0,0) ++ [(1,0)])
  have h6 := root_countdown_cr_zero_step
    ([(1,0)] ++ List.replicate (4*n+6) (0,0) ++ [(1,0)]) []
  have h7 := root_countdown_cr_one_zero_step
    (List.replicate (4*n+5) (0,0) ++ [(1,0)])
  have h7' : ReachesPlus target
      (cfg_CR_n_n
        ([(1,0),(0,0)] ++ List.replicate (4*n+5) (0,0) ++ [(1,0)])
        [(2,0)])
      (cfg_CR_n_n
        (List.replicate (4*n+5) (0,0) ++ [(1,0)])
        [(0,0),(5,0)]) := h7
  have h8 := root_countdown_cr_zero_sweep_pair (4*n+4) 0 [(1,0)] [(5,0)]
  have h9 := root_countdown_cr_one_empty_step [(8*n+10,0),(5,0)]
  have h10 := root_countdown_general_tail_with_suffix (8*n+13) [(5,0)] (by omega)
  have hx : 8*n+13-6 = 8*n+7 := by omega
  have h10' : ReachesPlus target
      (cfg_EL_n_n [(0,0)] [(0,0),(8*n+13,0),(5,0)])
      (cfg_CR_n_n [(0,0)]
        (List.replicate 5 (0,0) ++ [(8*n+7,0),(5,0)])) := by
    simpa [hx] using h10
  exact ReachesPlus.trans h1
    (ReachesPlus.trans h2'
      (ReachesPlus.trans h3
        (ReachesPlus.trans h4
          (ReachesPlus.trans h5
            (ReachesPlus.trans h6
              (ReachesPlus.trans h7'
                (ReachesPlus.trans h8
                  (ReachesPlus.trans h9 h10'))))))))

theorem root_countdown_one_five_reset (n : ℕ) :
    ReachesPlus target
      (cfg_CR_n_n [(0,0)]
        (List.replicate (4*n+5) (0,0) ++ [(1,0),(5,0)]))
      (cfg_CR_n_n [(0,0)]
        (List.replicate 5 (0,0) ++ [(8*n+11,0)] ++
          List.replicate 3 (0,0) ++ [(2,0)])) := by
  have h1 := root_countdown_prefix_with_tail_fixed n 1 [(5,0)]
  have h2 := root_countdown_el_zero_sweep (4*n+5) [(0,0),(1,0)] [(1,0),(5,0)]
  have h2' : ReachesPlus target
      (cfg_EL_n_n [(0,0),(1,0)]
        (List.replicate (4*n+6) (0,0) ++ [(1,0),(5,0)]))
      (cfg_EL_n_n (List.replicate (4*n+7) (0,0) ++ [(1,0)]) [(1,0),(5,0)]) := by
    simpa [List.replicate_succ, List.cons_append, List.append_assoc] using h2
  have h3 := root_countdown_el_positive_step 0
    (List.replicate (4*n+7) (0,0) ++ [(1,0)]) [(5,0)]
  have h4 := root_countdown_dl_zero_step
    (List.replicate (4*n+7) (0,0) ++ [(1,0)]) [(5,0)]
  have h5 := root_countdown_el_positive_step 4
    ([(0,0),(1,0)] ++ List.replicate (4*n+6) (0,0) ++ [(1,0)]) []
  have h6 := root_countdown_dl_positive_step 2
    ([(0,0),(1,0)] ++ List.replicate (4*n+6) (0,0) ++ [(1,0)]) []
  have h7 := root_countdown_dr_zero_step
    ([(1,0)] ++ List.replicate (4*n+6) (0,0) ++ [(1,0)]) [(2,0)]
  have h8 := root_countdown_dr_positive_positive_step 0 0
    (List.replicate (4*n+6) (0,0) ++ [(1,0)]) [(0,0),(2,0)]
  have h9 := root_countdown_cr_zero_sweep_pair (4*n+6) 0 [(1,0)]
    (List.replicate 3 (0,0) ++ [(2,0)])
  have h10 := root_countdown_cr_one_empty_step
    [(8*n+14,0),(0,0),(0,0),(0,0),(2,0)]
  have h11 := root_countdown_general_tail_with_suffix (8*n+17)
    (List.replicate 3 (0,0) ++ [(2,0)]) (by omega)
  have hx : 8*n+17-6 = 8*n+11 := by omega
  have h11' : ReachesPlus target
      (cfg_EL_n_n [(0,0)]
        ([(0,0),(8*n+17,0)] ++ List.replicate 3 (0,0) ++ [(2,0)]))
      (cfg_CR_n_n [(0,0)]
        (List.replicate 5 (0,0) ++ [(8*n+11,0)] ++
          List.replicate 3 (0,0) ++ [(2,0)])) := by
    simpa [hx, List.append_assoc] using h11
  exact ReachesPlus.trans h1
    (ReachesPlus.trans h2'
      (ReachesPlus.trans h3
        (ReachesPlus.trans h4
          (ReachesPlus.trans h5
            (ReachesPlus.trans h6
              (ReachesPlus.trans h7
                (ReachesPlus.trans h8
                  (ReachesPlus.trans h9
                    (ReachesPlus.trans h10 h11')))))))))
