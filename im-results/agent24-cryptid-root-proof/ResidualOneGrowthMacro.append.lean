/-!
Source-local append theorem for the residual-one growth macro.
Append this file inside the pinned source module
M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA, after its local
`tstep`/`texecute` macros and private `tok_DR` definition.

This is intentionally a single direct kernel proof over the actual source
step function. It does not use the generic existential
`tok_DR_2_0_closed` theorem.
-/

private theorem agent24_tok_DR_growth_step (s : ℕ) :
    (tok_DR [2,0] [(s,0)] [0]) [target]⊢⁺
      (tok_DR [2,0] [(s+5,0)] [0]) := by
  unfold tok_DR
  texecute 36

#print axioms agent24_tok_DR_growth_step

private theorem agent24_tok_DR_growth_iter (s k : ℕ) :
    (tok_DR [2,0] [(s,0)] [0]) [target]⊢⁺
      (tok_DR [2,0] [(s + 5 * (k + 1),0)] [0]) := by
  induction k with
  | zero =>
      simpa using agent24_tok_DR_growth_step s
  | succ k ih =>
      have hstep := agent24_tok_DR_growth_step (s + 5 * (k + 1))
      simpa [Nat.mul_succ, Nat.add_assoc] using ReachesPlus.trans ih hstep

#print axioms agent24_tok_DR_growth_iter

/-- The residual-one branch of the S-family token normalizer. -/
private theorem agent24_s_residual_one_to_cr (k : ℕ) (R3 : List (ℕ × ℕ)) :
    (tok_DR [2,1,1,1,1,1,0] R3 (List.replicate (k+1) 0 ++ [1]))
      [target]⊢⁺
    (cfg_CR_n_n
      (List.replicate (k+10) (0,0) ++ [(1,0)]) (bumpPairHead R3)) := by
  have h1 := root_d2_tok_dr_zero_sweep k [1,1,1,1,1,0] R3 [1]
  have h2 :
      ReachesPlus target
        (tok_DR (2 :: List.replicate (k+1) 1 ++ [1,1,1,1,1,0]) R3 [1])
        (tok_EL (List.replicate (k+7) 1 ++ [0]) R3 [0,0,0,1]) := by
    simpa [List.replicate_succ, List.cons_append, List.append_assoc] using
      (tok_DR_1_nil_28 (List.replicate (k+1) 1 ++ [1,1,1,1,1,0]) R3)
  have h3 :
      ReachesPlus target
        (tok_EL (List.replicate (k+7) 1 ++ [0]) R3 [0,0,0,1])
        (tok_EL [0] R3 (List.replicate (k+10) 0 ++ [1])) := by
    simpa [List.replicate_succ, List.cons_append, List.append_assoc] using
      (root_d2_tok_el_one_sweep (k+6) [0] R3 [0,0,0,1])
  have h4 := tok_EL_exit_zero R3 (List.replicate (k+10) 0 ++ [1])
  simpa [List.map_replicate, List.map_append, List.replicate_succ,
    List.cons_append, List.append_assoc] using
    ReachesPlus.trans h1 (ReachesPlus.trans h2 (ReachesPlus.trans h3 h4))

/-- The source CR/EL/DL/DR tail maps the residual-one CR stack to T(2r+18). -/
private theorem agent24_cr_residual_one_to_growth (r : ℕ) :
    (cfg_CR_n_n
      (List.replicate (r+9) (0,0) ++ [(1,0)]) [(0,0)])
      [target]⊢⁺
    (tok_DR [2,0] [(2*r+18,0)] [0]) := by
  have h1 := root_countdown_cr_zero_sweep_singleton (r+8) 0 [(1,0)]
  have h2 := root_countdown_cr_one_empty_step [(2*r+18,0)]
  have h3 := root_countdown_el_zero_step [(0,0)] [(2*r+21,0)]
  have h4 := root_countdown_el_positive_step (2*r+20) [(0,0),(0,0)] []
  have h5 := root_countdown_dl_positive_step (2*r+18) [(0,0),(0,0)] []
  have h6 :
      ReachesPlus target
        (cfg_DR_n_n [(0,0),(0,0)] [(1,0),(2*r+18,0)])
        (tok_DR [2,0] [(2*r+18,0)] [0]) := by
    unfold cfg_DR_n_n tok_DR
    rw [encRight_mod1 0 0 [(0,0)], Nat.mod_one 0, encRight_d0_s0 [(0,0)],
      encLeft_mod1 0 0 [(2*r+18,0)], Nat.mod_one 0, encLeft_d0_s0 [(2*r+18,0)],
      encRight_eq_nat [(0,0)],
      encTokens_succ, encTokens_succ, encTokens_zero, encTokens_zero, encTokens_nil]
    texecute 4
  simpa [bumpPairHead, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    ReachesPlus.trans h1 (ReachesPlus.trans h2
      (ReachesPlus.trans h3 (ReachesPlus.trans h4 (ReachesPlus.trans h5 h6))))

/-- Every residual-one S-family token state reaches the infinite-growth family. -/
private theorem agent24_s_residual_one_to_growth (k : ℕ) :
    (tok_DR [2,1,1,1,1,1,0] [] (List.replicate (k+1) 0 ++ [1]))
      [target]⊢⁺
    (tok_DR [2,0] [(2*(k+1)+18,0)] [0]) := by
  have h1 := agent24_s_residual_one_to_cr k []
  have h2 := agent24_cr_residual_one_to_growth (k+1)
  simpa [bumpPairHead, Nat.mul_add, Nat.add_assoc] using ReachesPlus.trans h1 h2

#print axioms agent24_s_residual_one_to_cr
#print axioms agent24_cr_residual_one_to_growth
#print axioms agent24_s_residual_one_to_growth
