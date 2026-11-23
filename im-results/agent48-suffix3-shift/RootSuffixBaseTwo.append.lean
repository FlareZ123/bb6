/-!
Exact source-branch draft for the residual-two singleton suffix.
Append AFTER RootSuffixThreeShift.append.lean and RootSuffixBaseZero.append.lean
before the original Cryptids #85 module's \`end\`.

No other research append is imported. All underlying token lemmas are the
PRIVATE ORIGINAL-SOURCE tok_DR_zero, tok_DR_1_nil_28, tok_EL_1,
tok_EL_exit_zero, and original cfg/tape definitions.
Status: uncompiled, not axiom audited; no sorry added.
-/

private theorem s3_nat_push (d k : ℕ) (L : List ℕ) :
    List.replicate k d ++ (d::L) =
      d::(List.replicate k d ++ L) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simpa only [List.replicate_succ, List.cons_append] using
        congrArg (List.cons d) ih

private theorem s3_nat_replicate_next (d k : ℕ) (L : List ℕ) :
    List.replicate (k+2) d ++ L =
      d::(List.replicate (k+1) d ++ L) := by
  rw [show k+2 = (k+1)+1 by omega, List.replicate_add]
  simpa [s3_nat_push, List.cons_append, List.append_assoc] using
    (s3_nat_push d (k+1) L)

private theorem s3_tok_dr_zeros (k : ℕ) (K1 : List ℕ)
    (R3 : List (ℕ × ℕ)) (L : List ℕ) :
    ReachesPlus target
      (tok_DR (2::K1) R3 (List.replicate (k+1) 0 ++ L))
      (tok_DR (2::List.replicate (k+1) 1 ++ K1) R3 L) := by
  induction k generalizing K1 L with
  | zero =>
      simpa [List.replicate_succ, List.cons_append] using
        (tok_DR_zero K1 R3 L)
  | succ k ih =>
      have h1 :
          ReachesPlus target
            (tok_DR (2::K1) R3 (List.replicate (k+2) 0 ++ L))
            (tok_DR (2::1::K1) R3
              (List.replicate (k+1) 0 ++ L)) := by
        rw [s3_nat_replicate_next 0 k L]
        exact tok_DR_zero K1 R3 (List.replicate (k+1) 0 ++ L)
      have h2 := ih (1::K1) L
      exact ReachesPlus.trans h1
        (by simpa [s3_nat_push, List.replicate_succ, List.cons_append,
          List.append_assoc] using h2)

private theorem s3_tok_el_ones (k : ℕ) (K1 : List ℕ)
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
            (tok_EL (List.replicate (k+1) 1 ++ K1)
              R3 (0::L)) := by
        rw [s3_nat_replicate_next 1 k K1]
        exact tok_EL_1 (List.replicate (k+1) 1 ++ K1) R3 L
      have h2 := ih K1 (0::L)
      exact ReachesPlus.trans h1
        (by simpa [s3_nat_push, List.replicate_succ, List.cons_append,
          List.append_assoc] using h2)

private theorem s3_tok_dr_z1 (k : ℕ) (R3 : List (ℕ × ℕ)) :
    ReachesPlus target
      (tok_DR [2,0] R3 (List.replicate (k+1) 0 ++ [1]))
      (cfg_CR_n_n
        ((List.replicate (k+5) 0 ++ [1]).map (fun x => (x,0)))
        (bumpPairHead R3)) := by
  have h1 := s3_tok_dr_zeros k [0] R3 [1]
  have h2 :
      ReachesPlus target
        (tok_DR (2::List.replicate (k+1) 1 ++ [0]) R3 [1])
        (tok_EL (List.replicate (k+2) 1 ++ [0])
          R3 [0,0,0,1]) := by
    have hr : List.replicate (k+2) 1 ++ [0] =
        1::(List.replicate (k+1) 1 ++ [0]) :=
      s3_nat_replicate_next 1 k [0]
    rw [hr]
    simpa only [List.cons_append] using
      (tok_DR_1_nil_28 (List.replicate (k+1) 1 ++ [0]) R3)
  have h3 :
      ReachesPlus target
        (tok_EL (List.replicate (k+2) 1 ++ [0])
          R3 [0,0,0,1])
        (tok_EL [0] R3 (List.replicate (k+5) 0 ++ [1])) := by
    have hz :
        List.replicate ((k+1)+1) 0 ++ [0,0,0,1] =
        List.replicate (k+5) 0 ++ [1] := by
      rw [show k+5=((k+1)+1)+3 by omega, List.replicate_add]
      simp [List.replicate_succ, List.cons_append, List.append_assoc]
    simpa [hz, s3_nat_push, List.replicate_succ, List.cons_append,
      List.append_assoc] using
      (s3_tok_el_ones (k+1) [0] R3 [0,0,0,1])
  have h4 := tok_EL_exit_zero R3
    (List.replicate (k+5) 0 ++ [1])
  exact ReachesPlus.trans h1
    (ReachesPlus.trans h2 (ReachesPlus.trans h3 h4))

private theorem s3_dl_one_z1 (k : ℕ) :
    ReachesPlus target
      (cfg_DL_0_n
        (List.replicate (k+1) (0,0) ++ [(1,0)]) [(1,0)])
      (cfg_CR_n_n
        (List.replicate (k+5) (0,0) ++ [(1,0)]) [(0,0)]) := by
  have h1 :
      ReachesPlus target
        (cfg_DL_0_n
          (List.replicate (k+1) (0,0) ++ [(1,0)]) [(1,0)])
        (tok_DR [2,0] [] (List.replicate (k+1) 0 ++ [1])) := by
    unfold cfg_DL_0_n tok_DR
    rw [encLeft_mod1 1 0 [], Nat.mod_one 0, encLeft_d1_s0 [],
      encRight_eq_nat (List.replicate (k+1) (0,0) ++ [(1,0)]),
      encTokens_succ, encTokens_succ, encTokens_zero,
      encTokens_zero, encTokens_nil]
    have hmap :
        List.map Prod.fst
          (List.replicate (k+1) (0,0) ++ [(1,0)]) =
        List.replicate (k+1) 0 ++ [1] := by
      simp
    rw [hmap]
    texecute 4
  have h2 := s3_tok_dr_z1 k []
  simpa [bumpPairHead, List.map_replicate, List.map_append] using
    (ReachesPlus.trans h1 h2)

/-- Corrected eight-successor source prefix for zero + suffix-two. -/
private theorem s3_two_prefix (n : ℕ) :
    ReachesPlus target
      (s3D n 2)
      (cfg_EL_n_n [(0,0),(1,0)]
        (List.replicate (4*n+6) (0,0) ++ [(0,0),(2,0)])) := by
  let tail : List (ℕ × ℕ) :=
    List.replicate (4*n+4) (0,0) ++ [(0,0),(2,0)]
  have h1 :
      ReachesPlus target
        (s3D n 2)
        (cfg_CR_n_n [] ((2,0)::tail)) := by
    simpa [s3D, tail, bumpPairHead, List.replicate_succ,
      List.cons_append, List.append_assoc] using
      (s3_cr_zero [] ((0,0)::tail))
  have h2 :
      ReachesPlus target
        (cfg_CR_n_n [] ((2,0)::tail))
        (cfg_EL_n_n [(0,0)] ((3,0)::tail)) := by
    simpa [bumpPairHead] using s3_cr_empty ((2,0)::tail)
  have h3 := s3_el_positive 2 [(0,0)] tail
  have h4 := s3_dl_positive 0 [(0,0)] tail
  have h5 := s3_dr_zero [] ((0,0)::tail)
  have h6 := s3_dr_empty ((1,0)::(0,0)::(0,0)::tail)
  have h7 := s3_el_positive 0 [(0,0)] ((0,0)::(0,0)::tail)
  have h8 :
      ReachesPlus target
        (cfg_DL_0_n [(0,0)]
          ((0,0)::(0,0)::(0,0)::tail))
        (cfg_EL_n_n [(0,0),(1,0)]
          ((0,0)::(0,0)::tail)) := by
    simpa [bumpPairHead] using
      (s3_dl_zero [(0,0)] ((0,0)::(0,0)::tail))
  simpa [tail, List.replicate_succ, List.cons_append,
    List.append_assoc, Nat.add_assoc] using
    (ReachesPlus.trans h1
      (ReachesPlus.trans h2
        (ReachesPlus.trans h3
          (ReachesPlus.trans h4
            (ReachesPlus.trans h5
              (ReachesPlus.trans h6
                (ReachesPlus.trans h7 h8)))))))

/-- Residual-two suffix source reset via the explicit DR/EL token cascade. -/
theorem s3_two_suffix_reset (n : ℕ) :
    ReachesPlus target
      (s3D n 2)
      (cfg_CR_n_n [(0,0)]
        (List.replicate 5 (0,0) ++ [(8*n+21,0)])) := by
  have h1 := s3_two_prefix n
  have h2 :
      ReachesPlus target
        (cfg_EL_n_n [(0,0),(1,0)]
          (List.replicate (4*n+6) (0,0) ++ [(0,0),(2,0)]))
        (cfg_EL_n_n
          (List.replicate (4*n+8) (0,0) ++ [(1,0)]) [(2,0)]) := by
    simpa [List.replicate_add, List.cons_append, List.append_assoc,
      Nat.add_assoc] using
      (s3_el_sweep (4*n+6) [(0,0),(1,0)] [(2,0)])
  have h3 := s3_el_positive 1
    (List.replicate (4*n+8) (0,0) ++ [(1,0)]) []
  have h4 := s3_dl_one_z1 (4*n+7)
  have h4' :
      ReachesPlus target
        (cfg_DL_0_n
          (List.replicate (4*n+8) (0,0) ++ [(1,0)]) [(1,0)])
        (cfg_CR_n_n
          (List.replicate (4*n+12) (0,0) ++ [(1,0)]) [(0,0)]) := by
    simpa [List.replicate_succ, List.cons_append,
      List.append_assoc, Nat.add_assoc] using h4
  have h5 :
      ReachesPlus target
        (cfg_CR_n_n
          (List.replicate (4*n+12) (0,0) ++ [(1,0)]) [(0,0)])
        (cfg_CR_n_n [(1,0)] [(8*n+24,0)]) := by
    have hc : 2*(4*n+12)=8*n+24 := by omega
    simpa [List.replicate_succ, List.cons_append,
      List.append_assoc, hc] using
      (s3_cr_zero_sweep (4*n+11) 0 [(1,0)])
  have h6 :
      ReachesPlus target
        (cfg_CR_n_n [(1,0)] [(8*n+24,0)])
        (cfg_EL_n_n [(0,0)] [(0,0),(8*n+27,0)]) := by
    simpa [bumpPairHead] using
      (s3_cr_one_empty [(8*n+24,0)])
  have h7 := s3_general_tail (8*n+27) (by omega)
  have hchain := ReachesPlus.trans h1
    (ReachesPlus.trans h2
      (ReachesPlus.trans h3
        (ReachesPlus.trans h4'
          (ReachesPlus.trans h5
            (ReachesPlus.trans h6 h7)))))
  simpa [List.replicate_succ, List.cons_append,
    List.append_assoc, Nat.add_assoc] using hchain

/-- The whole t ≡ 2 mod 3 singleton suffix class closes. -/
theorem s3_two_residue_family (k n : ℕ) :
    ReachesPlus target
      (s3D n (3*(k+1)+2))
      (cfg_CR_n_n [(0,0)]
        (List.replicate 5 (0,0) ++ [(8*(n+k+1)+21,0)])) := by
  have h1 := s3_iterated_suffix_shift k n 2
  have h2 := s3_two_suffix_reset (n+k+1)
  simpa [Nat.mul_add, Nat.mul_comm, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using ReachesPlus.trans h1 h2
