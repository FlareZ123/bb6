/-!
WITHDRAWN 2026-11-24: universal nonhalting claim is false.
See ../agent48-token-return-correction/README.md. Historical draft only.
Do not dispatch this proof target or use these declarations as accepted lemmas.
-/

/-!
Source-exact residual-one token recurrence for Cryptid #85.

The direct one-shot 36-step claim T(s) -> T(s+5) is false. The correct
recurrence is composed from a 15-step source token prefix to CR, the
source-local CR/EL/DL countdown helpers, and a final four-step DR-to-T
conversion. It gives a positive-time return from T(s) to T(s+5), and the
family invariant then proves NeverHaltsFrom at every T(s). This is a
token-family result, not a blank-root reachability claim.

Append after the corrected RootCountdownSweep fragment inside the pinned
source module. The token-state wrapper below is written explicitly because
the original tok_DR abbreviation is private to the upstream source file.
-/

/-- T(s) = tok_DR [2,0] [(s,0)] [0], exposed without private abbreviations. -/
def s3_tok_growth_cfg (s : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((([1] : List (Fin 2)) ^ 2) +>
    ((0 : Fin 2) >> ((0 : Fin 2) >> encLeft [(s,0)])))
      {{D}}> ((1 : Fin 2) >> ((0 : Fin 2) >> default))

/-- The token subroutine reaches CR([0,0,1],[s+1]) in 15 source steps. -/
theorem s3_tok_growth_to_CR (s : ℕ) :
    ReachesPlus target (s3_tok_growth_cfg s)
      (cfg_CR_n_n [(0,0),(0,0),(1,0)] [(s+1,0)]) := by
  unfold s3_tok_growth_cfg cfg_CR_n_n
  texecute 15

/-- CR([0,0,1],[s+1]) returns to T(s+5) by the checked countdown macros. -/
theorem s3_CR_to_growth_step5 (s : ℕ) :
    ReachesPlus target
      (cfg_CR_n_n [(0,0),(0,0),(1,0)] [(s+1,0)])
      (s3_tok_growth_cfg (s+5)) := by
  have h1 := root_countdown_cr_zero_sweep_singleton 1 (s+1) [(1,0)]
  have h2 := root_countdown_cr_one_empty_step [(s+5,0)]
  have h3 := root_countdown_el_zero_step [(0,0)] [(s+8,0)]
  have h4 := root_countdown_el_positive_step (s+7) [(0,0),(0,0)] []
  have h5 := root_countdown_dl_positive_step (s+5) [(0,0),(0,0)] []
  have h6 : ReachesPlus target
      (cfg_DR_n_n [(0,0),(0,0)] [(1,0),(s+5,0)])
      (s3_tok_growth_cfg (s+5)) := by
    unfold s3_tok_growth_cfg cfg_DR_n_n
    texecute 4
  have h := ReachesPlus.trans h1
    (ReachesPlus.trans h2
      (ReachesPlus.trans h3
        (ReachesPlus.trans h4 (ReachesPlus.trans h5 h6))))
  simpa [bumpPairHead, Nat.add_assoc] using h

/-- Correct positive-time recurrence: T(s) reaches T(s+5). -/
theorem s3_tok_growth_step5 (s : ℕ) :
    ReachesPlus target (s3_tok_growth_cfg s) (s3_tok_growth_cfg (s+5)) :=
  ReachesPlus.trans (s3_tok_growth_to_CR s) (s3_CR_to_growth_step5 s)

/-- The entire T-family is closed under a positive-time successor. -/
theorem s3_tok_growth_never_halts (s : ℕ) :
    NeverHaltsFrom target (s3_tok_growth_cfg s) := by
  refine NeverHaltsFrom.of_reachesPlus_invariant
    (P := fun c => ∃ k : ℕ, c = s3_tok_growth_cfg k) ?_ ⟨s, rfl⟩
  rintro _ ⟨k, rfl⟩
  exact ⟨s3_tok_growth_cfg (k+5), s3_tok_growth_step5 k, ⟨k+5, rfl⟩⟩

#print axioms s3_tok_growth_to_CR
#print axioms s3_CR_to_growth_step5
#print axioms s3_tok_growth_step5
#print axioms s3_tok_growth_never_halts
