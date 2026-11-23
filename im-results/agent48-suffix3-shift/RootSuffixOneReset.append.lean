/-!
# Residual-one suffix reset for Cryptid D

This append is intended to be concatenated after the source-local suffix-three
shift fragment inside the pinned original Cryptids source module. It proves the
prepared suffix-one bridge directly from the same source-local mode clauses,
without depending on the uncompiled shared RootCountdownSweep draft.
-/

private def s3oD (n c : ℕ) (T : List (ℕ × ℕ)) : Cfg :=
  cfg_CR_n_n [(0,0)]
    (List.replicate (4*n+5) (0,0) ++ [(0,0),(c,0)] ++ T)

private theorem s3o_cr_one_zero (L : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_CR_n_n ((1,0)::(0,0)::L) [(2,0)])
      (cfg_CR_n_n L [(0,0),(5,0)]) := by
  unfold cfg_CR_n_n
  rw [encLeft_run_s0 2 [], encRight_d1_s0 ((0,0)::L),
    encRight_d0_s0 L, encLeft_d0_s0 [(5,0)], encLeft_run_s0 5 []]
  execute 5

private theorem s3o_cr_one_empty (R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_CR_n_n [(1,0)] R)
      (cfg_EL_n_n [(0,0)]
        ((0,0)::bumpPairHead (bumpPairHead (bumpPairHead R)))) := by
  unfold cfg_CR_n_n cfg_EL_n_n
  rw [encRight_mod1 1 0 [], Nat.mod_one 0, encRight_d1_s0 [],
    encRight_d0_s0 [],
    encLeft_d0_s0 (bumpPairHead (bumpPairHead (bumpPairHead R))),
    ← encLeft_cons_one (bumpPairHead (bumpPairHead R)),
    ← encLeft_cons_one (bumpPairHead R)]
  execute 6

private theorem s3o_el_empty (L : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_EL_n_n L [])
      (cfg_CR_n_n L [(0,0)]) := by
  unfold cfg_EL_n_n cfg_CR_n_n
  rw [encLeft_d0_s0 []]
  execute 1

private theorem s3o_cr_zero_sweep_pair (k b : ℕ)
    (L R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_CR_n_n (List.replicate (k+1) (0,0) ++ L) ((b,0)::R))
      (cfg_CR_n_n L ((b+2*(k+1),0)::R)) := by
  induction k generalizing b L R with
  | zero =>
      simpa [bumpPairHead] using (s3_cr_zero L ((b,0)::R))
  | succ k ih =>
      have h1 := s3_cr_zero
        (List.replicate (k+1) (0,0) ++ L) ((b,0)::R)
      have h1' :
          ReachesPlus target
            (cfg_CR_n_n (List.replicate (k+2) (0,0) ++ L) ((b,0)::R))
            (cfg_CR_n_n (List.replicate (k+1) (0,0) ++ L) ((b+2,0)::R)) := by
        simpa [List.replicate_succ, List.cons_append,
          List.append_assoc, bumpPairHead] using h1
      have h2 := ih (b+2) L R
      have h2' :
          ReachesPlus target
            (cfg_CR_n_n (List.replicate (k+1) (0,0) ++ L) ((b+2,0)::R))
            (cfg_CR_n_n L ((b+2*(k+2),0)::R)) := by
        have hval : b+2+2*(k+1) = b+2*(k+2) := by omega
        simpa [hval] using h2
      exact ReachesPlus.trans h1' h2'

private theorem s3o_prefix (n c : ℕ) (T : List (ℕ × ℕ)) :
    ReachesPlus target
      (s3oD n c T)
      (cfg_EL_n_n [(0,0),(1,0)]
        (List.replicate (4*n+6) (0,0) ++ [(0,0),(c,0)] ++ T)) := by
  let tail : List (ℕ × ℕ) :=
    List.replicate (4*n+4) (0,0) ++ [(0,0),(c,0)] ++ T
  have h1 :
      ReachesPlus target
        (s3oD n c T)
        (cfg_CR_n_n [] ((2,0)::tail)) := by
    simpa [s3oD, tail, bumpPairHead, List.replicate_succ,
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

private theorem s3o_general_tail (x : ℕ) (T : List (ℕ × ℕ))
    (hx : 6 ≤ x) :
    ReachesPlus target
      (cfg_EL_n_n [(0,0)] ((0,0)::(x,0)::T))
      (cfg_CR_n_n [(0,0)]
        (List.replicate 5 (0,0) ++ [(x-6,0)] ++ T)) := by
  have hx1 : x-1+1 = x := by omega
  have hx2 : x-3+2 = x-1 := by omega
  have hx3 : x-4+1 = x-3 := by omega
  have hx4 : x-6+2 = x-4 := by omega
  have h1 := s3_el_zero [(0,0)] ((x,0)::T)
  have h2 := s3_el_positive (x-1) [(0,0),(0,0)] T
  have h2' :
      ReachesPlus target
        (cfg_EL_n_n [(0,0),(0,0)] ((x,0)::T))
        (cfg_DL_0_n [(0,0),(0,0)] ((x-1,0)::T)) := by
    simpa [hx1] using h2
  have h3 := s3_dl_positive (x-3) [(0,0),(0,0)] T
  have h3' :
      ReachesPlus target
        (cfg_DL_0_n [(0,0),(0,0)] ((x-1,0)::T))
        (cfg_DR_n_n [(0,0),(0,0)] ((1,0)::(x-3,0)::T)) := by
    simpa [hx2] using h3
  have h4 := s3_dr_sweep 1 [] ((x-3,0)::T)
  have h5 := s3_dr_empty
    ((1,0)::(0,0)::(0,0)::(x-3,0)::T)
  have h6 := s3_el_positive 0 [(0,0)]
    ((0,0)::(0,0)::(x-3,0)::T)
  have h7 := s3_dl_zero [(0,0)]
    ((0,0)::(0,0)::(x-3,0)::T)
  have h8 := s3_el_sweep 1 [(0,0),(1,0)] ((x-3,0)::T)
  have h9 := s3_el_positive (x-4)
    [(0,0),(0,0),(0,0),(1,0)] T
  have h9' :
      ReachesPlus target
        (cfg_EL_n_n [(0,0),(0,0),(0,0),(1,0)] ((x-3,0)::T))
        (cfg_DL_0_n [(0,0),(0,0),(0,0),(1,0)] ((x-4,0)::T)) := by
    simpa [hx3] using h9
  have h10 := s3_dl_positive (x-6)
    [(0,0),(0,0),(0,0),(1,0)] T
  have h10' :
      ReachesPlus target
        (cfg_DL_0_n [(0,0),(0,0),(0,0),(1,0)] ((x-4,0)::T))
        (cfg_DR_n_n [(0,0),(0,0),(0,0),(1,0)]
          ((1,0)::(x-6,0)::T)) := by
    simpa [hx4] using h10
  have h11 := s3_dr_sweep 2 [(1,0)] ((x-6,0)::T)
  have h12 := s3_dr_positive_positive 0 0 []
    (List.replicate 3 (0,0) ++ (x-6,0)::T)
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
                      (ReachesPlus.trans h11 h12)))))))))

/-- The residual-one family Q(n,1;T) enters the suffix-five family. -/
theorem s3_residual_one_suffix_reset (n : ℕ) (T : List (ℕ × ℕ)) :
    ReachesPlus target
      (s3oD n 1 T)
      (cfg_CR_n_n [(0,0)]
        (List.replicate 5 (0,0) ++ [(8*n+9,0),(5,0)] ++ T)) := by
  have h1 := s3o_prefix n 1 T
  have h2 := s3_el_sweep (4*n+6) [(0,0),(1,0)] ((1,0)::T)
  have h2' :
      ReachesPlus target
        (cfg_EL_n_n [(0,0),(1,0)]
          (List.replicate (4*n+6) (0,0) ++ [(0,0),(1,0)] ++ T))
        (cfg_EL_n_n
          (List.replicate (4*n+8) (0,0) ++ [(1,0)])
          T) := by
    simpa [List.replicate_add, List.cons_append,
      List.append_assoc, Nat.add_assoc] using h2
  have h3 := s3_el_positive 0
    (List.replicate (4*n+8) (0,0) ++ [(1,0)]) T
  have h4 := s3_dl_zero
    (List.replicate (4*n+8) (0,0) ++ [(1,0)]) T
  have h5 := s3o_el_empty
    ((0,0)::bumpPairHead
      (List.replicate (4*n+8) (0,0) ++ [(1,0)]))
  have h6 := s3_cr_zero
    (bumpPairHead
      (List.replicate (4*n+8) (0,0) ++ [(1,0)]))
    [(0,0)]
  have h7 := s3o_cr_one_zero
    (List.replicate (4*n+6) (0,0) ++ [(1,0)])
  have h8 := s3o_cr_zero_sweep_pair (4*n+5) 0 [(1,0)]
    ((5,0)::T)
  have h9 := s3o_cr_one_empty ((8*n+12,0)::(5,0)::T)
  have h10 := s3o_general_tail (8*n+15) ((5,0)::T) (by omega)
  exact ReachesPlus.trans h1
    (ReachesPlus.trans h2'
      (ReachesPlus.trans h3
        (ReachesPlus.trans h4
          (ReachesPlus.trans h5
            (ReachesPlus.trans h6
              (ReachesPlus.trans h7
                (ReachesPlus.trans h8
                  (ReachesPlus.trans h9 h10)))))))
