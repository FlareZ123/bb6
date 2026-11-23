/-!
The universal suffix-three shift with an arbitrary further pair-stack tail.
Append after RootSuffixThreeShift.append.lean, inside the original pinned
DeepMind #85 module. Original source clauses only; no sorry or axiom.
NOT YET COMPILED. This strengthens the empty-tail theorem to finite words.
-/

/-- A zero-counter section with a two-digit prefix and arbitrary tail. -/
def s3DWord (n t : ℕ) (T : List (ℕ × ℕ)) : Cfg (Fin 2) (Fin 6) :=
  cfg_CR_n_n [(0,0)]
    (List.replicate (4*n+5) (0,0) ++ [(0,0),(t,0)] ++ T)

/-- Corrected source prefix with an arbitrary untouched suffix context. -/
private theorem s3_word_prefix (n t : ℕ) (T : List (ℕ × ℕ)) :
    ReachesPlus target
      (s3DWord n (t+3) T)
      (cfg_EL_n_n [(0,0),(1,0)]
        (List.replicate (4*n+6) (0,0) ++ [(0,0),(t+3,0)] ++ T)) := by
  let tail : List (ℕ × ℕ) :=
    List.replicate (4*n+4) (0,0) ++ [(0,0),(t+3,0)] ++ T
  have h1 :
      ReachesPlus target
        (s3DWord n (t+3) T)
        (cfg_CR_n_n [] ((2,0)::tail)) := by
    simpa [s3DWord, tail, bumpPairHead, List.replicate_succ,
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

/-- Shift three from the first nonzero suffix digit, preserving every later digit. -/
set_option maxHeartbeats 1000000 in
theorem s3_universal_word_suffix_shift (n t : ℕ)
    (T : List (ℕ × ℕ)) :
    ReachesPlus target (s3DWord n (t+3) T)
      (s3DWord (n+1) t T) := by
  have h1 := s3_word_prefix n t T
  have h2 :
      ReachesPlus target
        (cfg_EL_n_n [(0,0),(1,0)]
          (List.replicate (4*n+6) (0,0) ++ [(0,0),(t+3,0)] ++ T))
        (cfg_EL_n_n
          (List.replicate (4*n+8) (0,0) ++ [(1,0)])
          ((t+3,0)::T)) := by
    simpa [List.replicate_add, List.cons_append,
      List.append_assoc, Nat.add_assoc] using
      (s3_el_sweep (4*n+6) [(0,0),(1,0)] ((t+3,0)::T))
  have h3 := s3_el_positive (t+2)
    (List.replicate (4*n+8) (0,0) ++ [(1,0)]) T
  have h4 := s3_dl_positive t
    (List.replicate (4*n+8) (0,0) ++ [(1,0)]) T
  have h5 := s3_dr_sweep (4*n+7) [(1,0)] ((t,0)::T)
  have h6 := s3_dr_positive_positive 0 0 []
    (List.replicate (4*n+8) (0,0) ++ [(t,0)] ++ T)
  have h6' :
      ReachesPlus target
        (cfg_DR_n_n [(1,0)] ((1,0)::
          (List.replicate (4*n+8) (0,0) ++ [(t,0)] ++ T)))
        (s3DWord (n+1) t T) := by
    simpa [s3DWord, s3_zero_push, List.replicate_add, List.replicate_succ,
      List.cons_append, List.append_assoc, Nat.mul_add, Nat.add_assoc] using h6
  have hchain := ReachesPlus.trans h1
    (ReachesPlus.trans h2
      (ReachesPlus.trans h3
        (ReachesPlus.trans h4
          (ReachesPlus.trans h5 h6'))))
  simpa [Nat.add_assoc] using hchain

/-- Arbitrarily long suffix-word 3-adic reduction without touching T. -/
theorem s3_iterated_word_suffix_shift (k n t : ℕ)
    (T : List (ℕ × ℕ)) :
    ReachesPlus target
      (s3DWord n (t+3*(k+1)) T)
      (s3DWord (n+k+1) t T) := by
  induction k generalizing n with
  | zero =>
      simpa using s3_universal_word_suffix_shift n t T
  | succ k ih =>
      have h1 := s3_universal_word_suffix_shift
        n (t+3*(k+1)) T
      have h2 := ih (n+1)
      have ht : t + 3*((k+1)+1) = t + 3*(k+1) + 3 := by omega
      have hn : n + ((k+1)+1) = (n+1) + (k+1) := by omega
      rw [ht, hn]
      exact ReachesPlus.trans h1 h2
