/-!
Uniform source-connected odd zero-run suffix-[2] closure.

Append AFTER RootSuffixThreeShift, RootSuffixBaseZero,
RootSuffixBaseTwo in pinned Cryptid D module, before final namespace end.

The base token closure is the independently sourced s3_dl_one_z1.
STATUS: draft, not yet compiled or kernel audited.
-/

def s3_padded_two (u : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_CR_n_n [(0,0)] (List.replicate (u+1) (0,0) ++ [(2,0)])

/-- Exact source 8-step prefix independent of any 4n+5 alignment. -/
private theorem s3_padded_two_prefix (u : ℕ) :
    ReachesPlus target
      (s3_padded_two u)
      (cfg_EL_n_n [(0,0),(1,0)]
        (List.replicate (u+2) (0,0) ++ [(2,0)])) := by
  let tail : List (ℕ × ℕ) := List.replicate u (0,0) ++ [(2,0)]
  have h1 :
      ReachesPlus target
        (s3_padded_two u)
        (cfg_CR_n_n [] ((2,0)::tail)) := by
    simpa [s3_padded_two, tail, bumpPairHead, List.replicate_succ,
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
        (cfg_DL_0_n [(0,0)] ((0,0)::(0,0)::(0,0)::tail))
        (cfg_EL_n_n [(0,0),(1,0)] ((0,0)::(0,0)::tail)) := by
    simpa [bumpPairHead] using
      (s3_dl_zero [(0,0)] ((0,0)::(0,0)::tail))
  have hchain := ReachesPlus.trans h1
    (ReachesPlus.trans h2
      (ReachesPlus.trans h3
        (ReachesPlus.trans h4
          (ReachesPlus.trans h5
            (ReachesPlus.trans h6
              (ReachesPlus.trans h7 h8))))))
  simpa [tail, List.replicate_add, List.replicate_succ,
    List.cons_append, List.append_assoc, Nat.add_assoc] using hchain

/-- The full source TM has a closed reset for ANY positive zero-run length. -/
theorem s3_padded_two_reset (u : ℕ) :
    ReachesPlus target
      (s3_padded_two u)
      (cfg_CR_n_n [(0,0)]
        (List.replicate 5 (0,0) ++ [(2*u+11,0)])) := by
  have h1 := s3_padded_two_prefix u
  have h2raw := s3_el_sweep (u+1) [(0,0),(1,0)] [(2,0)]
  have h2 :
      ReachesPlus target
        (cfg_EL_n_n [(0,0),(1,0)]
          (List.replicate (u+2) (0,0) ++ [(2,0)]))
        (cfg_EL_n_n
          (List.replicate (u+3) (0,0) ++ [(1,0)]) [(2,0)]) := by
    simpa [s3_zero_push, List.replicate_succ, List.replicate_add,
      List.cons_append, List.append_assoc, Nat.add_assoc] using h2raw
  have h3 := s3_el_positive 1
    (List.replicate (u+3) (0,0) ++ [(1,0)]) []
  have h4raw := s3_dl_one_z1 (u+2)
  have h4 :
      ReachesPlus target
        (cfg_DL_0_n
          (List.replicate (u+3) (0,0) ++ [(1,0)]) [(1,0)])
        (cfg_CR_n_n
          (List.replicate (u+7) (0,0) ++ [(1,0)]) [(0,0)]) := by
    simpa [List.replicate_succ, List.cons_append,
      List.append_assoc, Nat.add_assoc] using h4raw
  have h5raw := s3_cr_zero_sweep (u+6) 0 [(1,0)]
  have h5 :
      ReachesPlus target
        (cfg_CR_n_n
          (List.replicate (u+7) (0,0) ++ [(1,0)]) [(0,0)])
        (cfg_CR_n_n [(1,0)] [(2*u+14,0)]) := by
    simpa [List.replicate_succ, List.cons_append,
      List.append_assoc, Nat.mul_add, Nat.add_assoc] using h5raw
  have h6 :
      ReachesPlus target
        (cfg_CR_n_n [(1,0)] [(2*u+14,0)])
        (cfg_EL_n_n [(0,0)] [(0,0),(2*u+17,0)]) := by
    simpa [bumpPairHead, Nat.add_assoc] using
      (s3_cr_one_empty [(2*u+14,0)])
  have h7 := s3_general_tail (2*u+17) (by omega)
  have hchain := ReachesPlus.trans h1
    (ReachesPlus.trans h2
      (ReachesPlus.trans h3
        (ReachesPlus.trans h4
          (ReachesPlus.trans h5
            (ReachesPlus.trans h6 h7)))))
  simpa [Nat.mul_add, Nat.add_assoc] using hchain

/-- Application to any even padding beyond the 4n+6 canonical zero-run. -/
theorem s3_padded_two_even_extension (n q : ℕ) :
    ReachesPlus target
      (cfg_CR_n_n [(0,0)]
        (List.replicate (4*n+6+2*q) (0,0) ++ [(2,0)]))
      (cfg_CR_n_n [(0,0)]
        (List.replicate 5 (0,0) ++ [(8*n+21+4*q,0)])) := by
  have h := s3_padded_two_reset (4*n+5+2*q)
  simpa [s3_padded_two, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm] using h
