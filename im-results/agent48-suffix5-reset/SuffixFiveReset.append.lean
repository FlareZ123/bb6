/-!
Source-local draft for the #85 suffix-[5] zero branch.
Append AFTER RootCountdownSweep.append.lean and RootRemainderTwoToken.append.lean
to the pinned Cryptids module. No sorry or axioms are introduced.
NOT YET COMPILED or axiom audited.
-/

/-- The suffix-[0,2] zero branch closes through the known DL token Z1 lemma. -/
theorem root_suffix_zero_two_reset (n : ℕ) :
    ReachesPlus target
      (cfg_CR_n_n [(0,0)]
        (List.replicate (4*n+5) (0,0) ++ [(0,0),(2,0)]))
      (cfg_CR_n_n [(0,0)]
        (List.replicate 5 (0,0) ++ [(8*n+21,0)])) := by
  have h1 := root_countdown_prefix_with_tail_fixed n 0 [(2,0)]
  have h2 :
      ReachesPlus target
        (cfg_EL_n_n [(0,0),(1,0)]
          (List.replicate (4*n+6) (0,0) ++ [(0,0),(2,0)]))
        (cfg_EL_n_n
          (List.replicate (4*n+8) (0,0) ++ [(1,0)]) [(2,0)]) := by
    simpa [List.replicate_succ, List.cons_append, List.append_assoc,
      Nat.add_assoc] using
      (root_countdown_el_zero_sweep (4*n+6) [(0,0),(1,0)] [(2,0)])
  have h3 := root_countdown_el_positive_step 1
    (List.replicate (4*n+8) (0,0) ++ [(1,0)]) []
  have h4 := root_d2_dl_one_z1 (4*n+7)
  have h5 :
      ReachesPlus target
        (cfg_CR_n_n
          (List.replicate (4*n+12) (0,0) ++ [(1,0)]) [(0,0)])
        (cfg_CR_n_n [(1,0)] [(8*n+24,0)]) := by
    have heq : 2*(4*n+12) = 8*n+24 := by omega
    simpa [List.replicate_succ, List.cons_append, List.append_assoc,
      heq] using
      (root_countdown_cr_zero_sweep_singleton (4*n+11) 0 [(1,0)])
  have h6 :
      ReachesPlus target
        (cfg_CR_n_n [(1,0)] [(8*n+24,0)])
        (cfg_EL_n_n [(0,0)] [(0,0),(8*n+27,0)]) := by
    simpa [bumpPairHead] using
      (root_countdown_cr_one_empty_step [(8*n+24,0)])
  have h7 := root_countdown_general_tail (8*n+27) (by omega)
  have h4' :
      ReachesPlus target
        (cfg_DL_0_n
          (List.replicate (4*n+8) (0,0) ++ [(1,0)]) [(1,0)])
        (cfg_CR_n_n
          (List.replicate (4*n+12) (0,0) ++ [(1,0)]) [(0,0)]) := by
    simpa [List.replicate_succ, List.cons_append, List.append_assoc,
      Nat.add_assoc] using h4
  have hchain := ReachesPlus.trans h1
    (ReachesPlus.trans h2
      (ReachesPlus.trans h3
        (ReachesPlus.trans h4'
          (ReachesPlus.trans h5 (ReachesPlus.trans h6 h7)))))
  simpa [List.replicate_succ, List.cons_append, List.append_assoc,
    Nat.add_assoc] using hchain

/-- Purely ordinary-mode bridge: D_n(0;[5]) -> D_(n+1)(0;[2]). -/
theorem root_suffix_five_to_zero_two (n : ℕ) :
    ReachesPlus target
      (cfg_CR_n_n [(0,0)]
        (List.replicate (4*n+5) (0,0) ++ [(0,0),(5,0)]))
      (cfg_CR_n_n [(0,0)]
        (List.replicate (4*(n+1)+5) (0,0) ++ [(0,0),(2,0)])) := by
  have h1 := root_countdown_prefix_with_tail_fixed n 0 [(5,0)]
  have h2 :
      ReachesPlus target
        (cfg_EL_n_n [(0,0),(1,0)]
          (List.replicate (4*n+6) (0,0) ++ [(0,0),(5,0)]))
        (cfg_EL_n_n
          (List.replicate (4*n+8) (0,0) ++ [(1,0)]) [(5,0)]) := by
    simpa [List.replicate_succ, List.cons_append, List.append_assoc,
      Nat.add_assoc] using
      (root_countdown_el_zero_sweep (4*n+6) [(0,0),(1,0)] [(5,0)])
  have h3 := root_countdown_el_positive_step 4
    (List.replicate (4*n+8) (0,0) ++ [(1,0)]) []
  have h4 := root_countdown_dl_positive_step 2
    (List.replicate (4*n+8) (0,0) ++ [(1,0)]) []
  have h5 := root_countdown_dr_zero_sweep (4*n+7) [(1,0)] [(2,0)]
  have h6 := root_countdown_dr_positive_positive_step 0 0 []
    (List.replicate (4*n+8) (0,0) ++ [(2,0)])
  have h6' :
      ReachesPlus target
        (cfg_DR_n_n [(1,0)]
          ((1,0) :: (List.replicate (4*n+8) (0,0) ++ [(2,0)])))
        (cfg_CR_n_n [(0,0)]
          (List.replicate (4*(n+1)+5) (0,0) ++ [(0,0),(2,0)])) := by
    simpa [List.replicate_succ, List.cons_append, List.append_assoc,
      Nat.mul_add, Nat.add_assoc] using h6
  have hchain := ReachesPlus.trans h1
    (ReachesPlus.trans h2
      (ReachesPlus.trans h3
        (ReachesPlus.trans h4
          (ReachesPlus.trans h5 h6'))))
  simpa [List.replicate_succ, List.cons_append, List.append_assoc,
    Nat.mul_add, Nat.add_assoc] using hchain

/-- Proposed source-local conclusion for the outstanding suffix-[5] branch. -/
theorem root_suffix_five_reset (n : ℕ) :
    ReachesPlus target
      (cfg_CR_n_n [(0,0)]
        (List.replicate (4*n+5) (0,0) ++ [(0,0),(5,0)]))
      (cfg_CR_n_n [(0,0)]
        (List.replicate 5 (0,0) ++ [(8*n+29,0)])) := by
  have h1 := root_suffix_five_to_zero_two n
  have h2 := root_suffix_zero_two_reset (n+1)
  simpa [Nat.mul_add, Nat.add_assoc] using ReachesPlus.trans h1 h2
