/-!
WITHDRAWN 2026-11-24: universal nonhalting claim is false.
See ../agent48-token-return-correction/README.md. Historical draft only.
Do not dispatch this proof target or use these declarations as accepted lemmas.
-/

/-!
Source-local closure of the residual-one S-family into the nonhalting T-family.

This fragment depends on the corrected RootCountdownSweep fragment,
RootRemainderTwoToken.append.lean, and RootTokenGrowthStep5.append.lean.
It does not establish blank-root reachability: it proves nonhalting only
for the parameterized residual-one seed family.
-/

/-- Explicit tape encoding of the residual-one seed S(k). -/
def s3_residual_one_cfg (k : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((([1,1,0,1,0,1,0,1,0,1,0,1,0,0] : List (Fin 2)) +> default)
    {{D}}>
    ((List.flatten (List.replicate (k+1) ([1,0] : List (Fin 2))) ++ [1,1,0]) +> default))

/-- S(k) reaches the exact CR countdown state. -/
theorem s3_residual_one_to_CR (k : ℕ) :
    ReachesPlus target (s3_residual_one_cfg k)
      (cfg_CR_n_n
        (List.replicate (k+9) (0,0) ++ [(1,0)]) [(0,0)]) := by
  have h1 := root_d2_tok_dr_zero_sweep k [1,1,1,1,1,0] [] [1]
  have h2 := tok_DR_1_nil_28 (List.replicate k 1 ++ [1,1,1,1,1,0]) []
  have h3 := root_d2_tok_el_one_sweep (k+5) [0] [] [0,0,0,1]
  have h4 := tok_EL_exit_zero [] (List.replicate (k+9) 0 ++ [1])
  have h := ReachesPlus.trans h1 (ReachesPlus.trans h2 (ReachesPlus.trans h3 h4))
  simpa [s3_residual_one_cfg, List.replicate_succ, List.cons_append,
    List.append_assoc, List.map_replicate, List.map_append, bumpPairHead] using h

/-- The countdown CR state returns to the token family with parameter 2r+18. -/
theorem s3_CR_to_T (r : ℕ) :
    ReachesPlus target
      (cfg_CR_n_n (List.replicate (r+9) (0,0) ++ [(1,0)]) [(0,0)])
      (s3_tok_growth_cfg (2*r+18)) := by
  let tail : List (ℕ × ℕ) := [(0,0),(0,0),(2*r+18,0)]
  have h1 := root_countdown_cr_zero_sweep_singleton (r+8) 0 [(1,0)]
  have h2 := root_countdown_cr_one_empty_step [(2*r+18,0)]
  have h3 := root_countdown_el_zero_step [(0,0)] [(2*r+21,0)]
  have h4 := root_countdown_el_positive_step (2*r+20) [(0,0),(0,0)] []
  have h5 := root_countdown_dl_positive_step (2*r+18) [(0,0),(0,0)] []
  have h6 : ReachesPlus target
      (cfg_DR_n_n [(0,0),(0,0)] [(1,0),(2*r+18,0)])
      (s3_tok_growth_cfg (2*r+18)) := by
    unfold s3_tok_growth_cfg cfg_DR_n_n
    texecute 4
  have h := ReachesPlus.trans h1
    (ReachesPlus.trans h2
      (ReachesPlus.trans h3
        (ReachesPlus.trans h4 (ReachesPlus.trans h5 h6))))
  simpa [tail, s3_tok_growth_cfg, bumpPairHead, Nat.add_assoc] using h

/-- Every residual-one S(k) reaches T(2k+18). -/
theorem s3_residual_one_to_T (k : ℕ) :
    ReachesPlus target (s3_residual_one_cfg k)
      (s3_tok_growth_cfg (2*k+18)) := by
  have h1 := s3_residual_one_to_CR k
  have h2 := s3_CR_to_T k
  simpa [s3_residual_one_cfg, s3_tok_growth_cfg, Nat.add_assoc,
    Nat.mul_add] using ReachesPlus.trans h1 h2

/-- The union of S(k) and T(s) is closed under positive-time successors. -/
theorem s3_residual_one_never_halts (k : ℕ) :
    NeverHaltsFrom target (s3_residual_one_cfg k) := by
  refine NeverHaltsFrom.of_reachesPlus_invariant
    (P := fun c =>
      (∃ j : ℕ, c = s3_residual_one_cfg j) ∨
      (∃ s : ℕ, c = s3_tok_growth_cfg s)) ?_ (Or.inl ⟨k, rfl⟩)
  rintro _ (⟨j, rfl⟩ | ⟨s, rfl⟩)
  · exact ⟨s3_tok_growth_cfg (2*j+18), s3_residual_one_to_T j,
      Or.inr ⟨2*j+18, rfl⟩⟩
  · exact ⟨s3_tok_growth_cfg (s+5), s3_tok_growth_step5 s,
      Or.inr ⟨s+5, rfl⟩⟩

#print axioms s3_residual_one_to_CR
#print axioms s3_CR_to_T
#print axioms s3_residual_one_to_T
#print axioms s3_residual_one_never_halts
