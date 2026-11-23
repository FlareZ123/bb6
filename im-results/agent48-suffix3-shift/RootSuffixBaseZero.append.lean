/-!
Source-local draft of the residual-zero base case for universal suffix shifting.

Append AFTER RootSuffixThreeShift.append.lean, before original DeepMind #85
module's final \`end\`. The only dependencies are the original module and
the s3_* source small-step theorems in the preceding file.
Not compiled; no sorry/axioms added.
-/

private theorem s3_cr_one_empty (R : List (ℕ × ℕ)) :
    ReachesPlus target (cfg_CR_n_n [(1,0)] R)
      (cfg_EL_n_n [(0,0)]
        ((0,0)::bumpPairHead (bumpPairHead (bumpPairHead R)))) := by
  unfold cfg_CR_n_n cfg_EL_n_n
  rw [encRight_mod1 1 0 [], Nat.mod_one 0, encRight_d1_s0 [],
    encRight_d0_s0 [],
    encLeft_d0_s0 (bumpPairHead (bumpPairHead (bumpPairHead R))),
    ← encLeft_cons_one (bumpPairHead (bumpPairHead R)),
    ← encLeft_cons_one (bumpPairHead R), ← encLeft_cons_one R]
  execute 6

private theorem s3_el_empty (L : List (ℕ × ℕ)) :
    ReachesPlus target (cfg_EL_n_n L []) (cfg_CR_n_n L [(0,0)]) := by
  unfold cfg_EL_n_n cfg_CR_n_n
  rw [encLeft_d0_s0 []]
  execute 1

private theorem s3_cr_zero_sweep (k b : ℕ) (L : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_CR_n_n (List.replicate (k+1) (0,0) ++ L) [(b,0)])
      (cfg_CR_n_n L [(b+2*(k+1),0)]) := by
  induction k generalizing b L with
  | zero =>
      simpa [bumpPairHead] using s3_cr_zero L [(b,0)]
  | succ k ih =>
      have h1 := s3_cr_zero
        (List.replicate (k+1) (0,0) ++ L) [(b,0)]
      have h2 := ih (b+2) L
      exact ReachesPlus.trans h1
        (by simpa [List.replicate_succ, List.cons_append, List.append_assoc,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h2)

/-- Corrected source-local 16-successor general end tail. -/
private theorem s3_general_tail (x : ℕ) (hx : 6 ≤ x) :
    ReachesPlus target
      (cfg_EL_n_n [(0,0)] [(0,0),(x,0)])
      (cfg_CR_n_n [(0,0)]
        (List.replicate 5 (0,0) ++ [(x-6,0)])) := by
  have h1 := s3_el_zero [(0,0)] [(x,0)]
  have h2 := s3_el_positive (x-1) [(0,0),(0,0)] []
  have h3 := s3_dl_positive (x-3) [(0,0),(0,0)] []
  have h4 := s3_dr_sweep 1 [] [(x-3,0)]
  have h5 := s3_dr_empty
    [(1,0),(0,0),(0,0),(x-3,0)]
  have h6 := s3_el_positive 0 [(0,0)]
    [(0,0),(0,0),(x-3,0)]
  have h7 := s3_dl_zero [(0,0)]
    [(0,0),(0,0),(x-3,0)]
  have h8 := s3_el_sweep 1 [(0,0),(1,0)]
    [(x-3,0)]
  have h9 := s3_el_positive (x-4)
    [(0,0),(0,0),(0,0),(1,0)] []
  have h10 := s3_dl_positive (x-6)
    [(0,0),(0,0),(0,0),(1,0)] []
  have h11 := s3_dr_sweep 2 [(1,0)] [(x-6,0)]
  have h12 := s3_dr_positive_positive 0 0 []
    (List.replicate 3 (0,0) ++ [(x-6,0)])
  have hx1 : x-1+1 = x := by omega
  have hx2 : x-3+2 = x-1 := by omega
  have hx3 : x-4+1 = x-3 := by omega
  have hx4 : x-6+2 = x-4 := by omega
  simpa [List.replicate_succ, List.cons_append, List.append_assoc,
    bumpPairHead, hx1, hx2, hx3, hx4] using
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

/-- The corrected 8-successor prefix also works for all-zero suffix. -/
private theorem s3_zero_prefix (n : ℕ) :
    ReachesPlus target
      (s3D n 0)
      (cfg_EL_n_n [(0,0),(1,0)]
        (List.replicate (4*n+8) (0,0))) := by
  let tail : List (ℕ × ℕ) :=
    List.replicate (4*n+4) (0,0) ++ [(0,0),(0,0)]
  have h1 :
      ReachesPlus target
        (s3D n 0)
        (cfg_CR_n_n [] ((2,0)::tail)) := by
    simpa [s3D, tail, bumpPairHead, List.replicate_succ,
      List.cons_append, List.append_assoc] using
      (s3_cr_zero [] (List.replicate (4*n+5) (0,0) ++ [(0,0),(0,0)]))
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
  simpa [tail, List.replicate_succ, List.cons_append, List.append_assoc,
    Nat.add_assoc] using
    (ReachesPlus.trans h1
      (ReachesPlus.trans h2
        (ReachesPlus.trans h3
          (ReachesPlus.trans h4
            (ReachesPlus.trans h5
              (ReachesPlus.trans h6
                (ReachesPlus.trans h7 h8)))))))

/-- Residual-zero singleton suffix closes to an explicit new D0 index. -/
theorem s3_zero_suffix_reset (n : ℕ) :
    ReachesPlus target
      (s3D n 0)
      (cfg_CR_n_n [(0,0)]
        (List.replicate 5 (0,0) ++ [(8*n+15,0)])) := by
  have h1 := s3_zero_prefix n
  have h2 := s3_el_sweep (4*n+7) [(0,0),(1,0)] []
  have h3 := s3_el_empty
    (List.replicate (4*n+8) (0,0) ++ [(0,0),(1,0)])
  have h4 :
      ReachesPlus target
        (cfg_CR_n_n
          (List.replicate (4*n+9) (0,0) ++ [(1,0)]) [(0,0)])
        (cfg_CR_n_n [(1,0)] [(8*n+18,0)]) := by
    have hcount : 2*(4*n+9)=8*n+18 := by omega
    simpa [List.replicate_succ, List.cons_append, List.append_assoc,
      hcount] using
      (s3_cr_zero_sweep (4*n+8) 0 [(1,0)])
  have h5 :
      ReachesPlus target
        (cfg_CR_n_n [(1,0)] [(8*n+18,0)])
        (cfg_EL_n_n [(0,0)] [(0,0),(8*n+21,0)]) := by
    simpa [bumpPairHead] using
      (s3_cr_one_empty [(8*n+18,0)])
  have h6 := s3_general_tail (8*n+21) (by omega)
  have h2' :
      ReachesPlus target
        (cfg_EL_n_n [(0,0),(1,0)] (List.replicate (4*n+8) (0,0)))
        (cfg_EL_n_n
          (List.replicate (4*n+8) (0,0) ++ [(0,0),(1,0)]) []) := by
    simpa [List.replicate_succ, List.cons_append, List.append_assoc]
      using h2
  have hchain := ReachesPlus.trans h1
    (ReachesPlus.trans h2'
      (ReachesPlus.trans h3
        (ReachesPlus.trans h4
          (ReachesPlus.trans h5 h6))))
  simpa [List.replicate_succ, List.cons_append, List.append_assoc,
    Nat.add_assoc] using hchain

/-- Entire t ≡ 0 mod 3 singleton suffix family resets. -/
theorem s3_zero_residue_family (k n : ℕ) :
    ReachesPlus target
      (s3D n (3*(k+1)))
      (cfg_CR_n_n [(0,0)]
        (List.replicate 5 (0,0) ++ [(8*(n+k+1)+15,0)])) := by
  have h1 := s3_iterated_suffix_shift k n 0
  have h2 := s3_zero_suffix_reset (n+k+1)
  simpa [Nat.mul_comm, Nat.add_assoc] using ReachesPlus.trans h1 h2
