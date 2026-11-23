/-!
Original-source Lean proof attempt for the residual-one token family.

The earlier proposed 36-step map T(s) -> T(s+5) is false. The exact
post-36 state is an intermediate D-state. A second 36-step source run
reaches a C-state with a two-step lasso (C on 1 -> F on 0 -> C on 1).
The three source theorems below check these two exact endpoints and the
lasso separately.

Append before the final namespace end of the pinned Cryptid #85 source
module; original private tok_DR and tstep are available there.
-/

/-- T(s) = tok_DR [2,0] [(s,0)] [0], exposed as a public Cfg. -/
def s3_tok_growth_cfg (s : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((([1] : List (Fin 2)) ^ 2) +>
    ((0 : Fin 2) >> ((0 : Fin 2) >> encLeft [(s,0)])))
      {{D}}> ((1 : Fin 2) >> ((0 : Fin 2) >> default))

/-- Exact original-source state after 36 primitive steps from T(s). -/
def s3_tok_growth_intermediate_cfg (s : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
    (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
    (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
    (1 : Fin 2) >> encLeft [(s,0)])
      {{D}}> ((1 : Fin 2) >> default)

/-- Exact original-source state after another 36 primitive steps. -/
def s3_tok_growth_cycle_cfg (s : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
    (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
    (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
    (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
    encLeft [(s,0)])
      {{C}}> ((1 : Fin 2) >> default)

/-- First 36-step segment, from the token state to the exact intermediate D-state. -/
theorem s3_tok_growth_36_to_intermediate (s : ℕ) :
    ReachesPlus target (s3_tok_growth_cfg s) (s3_tok_growth_intermediate_cfg s) := by
  unfold s3_tok_growth_cfg s3_tok_growth_intermediate_cfg
  iterate 36 tstep
  exact ⟨0, rfl⟩

/-- Second 36-step segment, from the intermediate D-state to the C-state. -/
theorem s3_tok_growth_36_to_cycle (s : ℕ) :
    ReachesPlus target (s3_tok_growth_intermediate_cfg s) (s3_tok_growth_cycle_cfg s) := by
  unfold s3_tok_growth_intermediate_cfg s3_tok_growth_cycle_cfg
  iterate 36 tstep
  exact ⟨0, rfl⟩

/-- The C-state on symbol 1 has a two-step lasso: C1 -> F0 -> C1. -/
theorem s3_tok_growth_cycle2 (s : ℕ) :
    ReachesPlus target (s3_tok_growth_cycle_cfg s) (s3_tok_growth_cycle_cfg s) := by
  unfold s3_tok_growth_cycle_cfg
  iterate 2 tstep
  exact ⟨0, rfl⟩

/-- Every T(s) reaches the source-level two-cycle in 74 primitive steps. -/
theorem s3_tok_growth_to_cycle (s : ℕ) :
    ReachesPlus target (s3_tok_growth_cfg s) (s3_tok_growth_cycle_cfg s) :=
  ReachesPlus.trans (s3_tok_growth_36_to_intermediate s)
    (ReachesPlus.trans (s3_tok_growth_36_to_cycle s) (s3_tok_growth_cycle2 s))

#print axioms s3_tok_growth_36_to_intermediate
#print axioms s3_tok_growth_36_to_cycle
#print axioms s3_tok_growth_cycle2
#print axioms s3_tok_growth_to_cycle
