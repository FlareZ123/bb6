/-!
Source-local, self-contained draft of a universal suffix-three shift for the
DeepMind #85 Cryptid D pair-stack accelerator.

Insert this file BEFORE the final \`end BusyBeaver.M_...\` of the exact
\`google-deepmind/cryptids@3647718b5df22e1a61462dec0376bd204526285a\`
source module. Only the original source clauses/encoders are used. No other
research append or unsound surrogate is imported.

STATUS: original-source proof DRAFT, not compiled or axiom-audited.
-/

/-- In the upstream CR coordinates, D_n(0;[t]) has exactly two explicit suffix digits. -/
def s3D (n t : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_CR_n_n [(0,0)] (List.replicate (4*n+5) (0,0) ++ [(0,0),(t,0)])

private theorem s3_cr_zero (L R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_CR_n_n ((0,0)::L) R)
      (cfg_CR_n_n L (bumpPairHead (bumpPairHead R))) := by
  unfold cfg_CR_n_n
  rw [encRight_mod1 0 0 L, Nat.mod_one 0, encRight_d0_s0 L,
    ← encLeft_cons_one (bumpPairHead R), ← encLeft_cons_one R]
  execute 2

private theorem s3_cr_empty (R : List (ℕ × ℕ)) :
    ReachesPlus target (cfg_CR_n_n [] R)
      (cfg_EL_n_n [(0,0)] (bumpPairHead R)) := by
  unfold cfg_CR_n_n cfg_EL_n_n
  rw [encRight_d0_s0 [], ← encLeft_cons_one R]
  execute 2

private theorem s3_el_positive (a : ℕ) (L R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_EL_n_n L ((a+1,0)::R))
      (cfg_DL_0_n L ((a,0)::R)) := by
  unfold cfg_EL_n_n cfg_DL_0_n
  rw [encLeft_mod1 (a+1) 0 R, Nat.mod_one 0, encLeft_succ a 0 R,
    encLeft_run_s0 a R]
  execute 1

private theorem s3_dl_positive (a : ℕ) (L R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_DL_0_n L ((a+2,0)::R))
      (cfg_DR_n_n L ((1,0)::(a,0)::R)) := by
  unfold cfg_DL_0_n cfg_DR_n_n
  rw [encLeft_mod1 (a+2) 0 R, Nat.mod_one 0,
    encLeft_succ (a+1) 0 R, encLeft_succ a 0 R,
    encLeft_run_s0 a R, encLeft_d1_s0 ((a,0)::R),
    encLeft_run_s0 R]
  execute 4

private theorem s3_dr_zero (L R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_DR_n_n ((0,0)::L) ((1,0)::R))
      (cfg_DR_n_n L ((1,0)::(0,0)::R)) := by
  unfold cfg_DR_n_n
  rw [encRight_mod1 0 0 L, Nat.mod_one 0, encRight_d0_s0 L,
    encLeft_mod1 1 0 R, Nat.mod_one 0, encLeft_succ 0 0 R,
    encLeft_run_s0 0 R, encLeft_d1_s0 ((0,0)::R),
    encLeft_run_s0 R]
  execute 4

private theorem s3_dr_empty (R : List (ℕ × ℕ)) :
    ReachesPlus target (cfg_DR_n_n [] R)
      (cfg_EL_n_n [(0,0)] R) := by
  unfold cfg_DR_n_n cfg_EL_n_n
  rw [encRight_d0_s0 []]
  execute 1

private theorem s3_dl_zero (L R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_DL_0_n L ((0,0)::R))
      (cfg_EL_n_n ((0,0)::bumpPairHead L) R) := by
  unfold cfg_DL_0_n cfg_EL_n_n
  rw [encLeft_mod1 0 0 R, Nat.mod_one 0, encLeft_d0_s0 R,
    encRight_d0_s0 (bumpPairHead L), ← encRight_cons_one L]
  execute 6

private theorem s3_dr_positive_positive (a b : ℕ) (L R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_DR_n_n ((a+1,0)::L) ((b+1,0)::R))
      (cfg_CR_n_n ((a,0)::L) ((0,0)::(b,0)::R)) := by
  unfold cfg_DR_n_n cfg_CR_n_n
  rw [encRight_mod1 (a+1) 0 L, Nat.mod_one 0,
    encRight_succ a 0 L, encRight_run_s0 a L,
    encLeft_mod1 (b+1) 0 R, Nat.mod_one 0,
    encLeft_succ b 0 R, encLeft_run_s0 b R,
    encLeft_d0_s0 ((b,0)::R), encLeft_run_s0 b R]
  execute 3

private theorem s3_el_zero (L R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_EL_n_n L ((0,0)::R))
      (cfg_EL_n_n ((0,0)::L) R) := by
  unfold cfg_EL_n_n
  rw [encLeft_mod1 0 0 R, Nat.mod_one 0, encLeft_d0_s0 R,
    encRight_d0_s0 L]
  execute 2

private theorem s3_el_sweep (k : ℕ) (L R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_EL_n_n L (List.replicate (k+1) (0,0) ++ R))
      (cfg_EL_n_n (List.replicate (k+1) (0,0) ++ L) R) := by
  induction k with
  | zero =>
    simpa using s3_el_zero L R
  | succ k ih =>
    have h1 := s3_el_zero L (List.replicate (k+1) (0,0) ++ R)
    have h2 := ih ((0,0)::L) R
    exact ReachesPlus.trans h1
      (by simpa [List.replicate_succ, List.cons_append,
        List.append_assoc] using h2)

private theorem s3_dr_sweep (k : ℕ) (L R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_DR_n_n (List.replicate (k+1) (0,0) ++ L) ((1,0)::R))
      (cfg_DR_n_n L ((1,0)::(List.replicate (k+1) (0,0) ++ R))) := by
  induction k with
  | zero =>
    simpa using s3_dr_zero L R
  | succ k ih =>
    have h1 := s3_dr_zero (List.replicate (k+1) (0,0) ++ L) R
    have h2 := ih L ((0,0)::R)
    exact ReachesPlus.trans h1
      (by simpa [List.replicate_succ, List.cons_append,
        List.append_assoc] using h2)

/-- Corrected eight-successor prefix, retaining the arbitrary singleton suffix. -/
private theorem s3_prefix (n t : ℕ) :
    ReachesPlus target
      (s3D n (t+3))
      (cfg_EL_n_n [(0,0),(1,0)]
        (List.replicate (4*n+6) (0,0) ++ [(0,0),(t+3,0)])) := by
  let tail : List (ℕ × ℕ) :=
    List.replicate (4*n+4) (0,0) ++ [(0,0),(t+3,0)]
  have h1 :
      ReachesPlus target
        (s3D n (t+3))
        (cfg_CR_n_n [] ((2,0)::tail)) := by
    simpa [s3D, tail, bumpPairHead, List.replicate_succ,
      List.cons_append, List.append_assoc] using
      (s3_cr_zero [] (List.replicate (4*n+5) (0,0) ++ [(0,0),(t+3,0)]))
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

/-- Universal original-source transition D_n(0;[t+3]) -> D_(n+1)(0;[t]). -/
theorem s3_universal_suffix_shift (n t : ℕ) :
    ReachesPlus target (s3D n (t+3)) (s3D (n+1) t) := by
  have h1 := s3_prefix n t
  have h2 :
      ReachesPlus target
        (cfg_EL_n_n [(0,0),(1,0)]
          (List.replicate (4*n+6) (0,0) ++ [(0,0),(t+3,0)]))
        (cfg_EL_n_n
          (List.replicate (4*n+8) (0,0) ++ [(1,0)])
          [(t+3,0)]) := by
    simpa [List.replicate_succ, List.cons_append,
      List.append_assoc, Nat.add_assoc] using
      (s3_el_sweep (4*n+6) [(0,0),(1,0)] [(t+3,0)])
  have h3 := s3_el_positive (t+2)
    (List.replicate (4*n+8) (0,0) ++ [(1,0)]) []
  have h4 := s3_dl_positive t
    (List.replicate (4*n+8) (0,0) ++ [(1,0)]) []
  have h5 := s3_dr_sweep (4*n+7) [(1,0)] [(t,0)]
  have h6 := s3_dr_positive_positive 0 0 []
    (List.replicate (4*n+8) (0,0) ++ [(t,0)])
  have h6' :
      ReachesPlus target
        (cfg_DR_n_n [(1,0)] ((1,0)::
          (List.replicate (4*n+8) (0,0) ++ [(t,0)])))
        (s3D (n+1) t) := by
    simpa [s3D, List.replicate_succ, List.cons_append,
      List.append_assoc, Nat.mul_add, Nat.add_assoc] using h6
  have hchain := ReachesPlus.trans h1
    (ReachesPlus.trans h2
      (ReachesPlus.trans h3
        (ReachesPlus.trans h4
          (ReachesPlus.trans h5 h6'))))
  simpa [Nat.add_assoc] using hchain

/-- For any positive k, remove k successive ternary digits from the suffix. -/
theorem s3_iterated_suffix_shift (k n t : ℕ) :
    ReachesPlus target
      (s3D n (t+3*(k+1))) (s3D (n+(k+1)) t) := by
  induction k generalizing n with
  | zero =>
      simpa using s3_universal_suffix_shift n t
  | succ k ih =>
      have h1 := s3_universal_suffix_shift n (t+3*(k+1))
      have h2 := ih (n+1)
      simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using ReachesPlus.trans h1 h2
