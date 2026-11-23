/-!
Original-source kernel preflight of the residual-one token branch.

The earlier proposed 36-step map from this token state to the same family
with parameter s+5 was falsified by original-source CI 45121831681. The
compiler's exact post-36 configuration is captured below as a new state
family. The next question is whether that state is a genuine short lasso.

Append before the final namespace end of the pinned Cryptid #85 source
module; original private tok_DR and tstep are available there.
-/

/-- The token state T(s) = tok_DR [2,0] [(s,0)] [0], exposed as a public Cfg. -/
def s3_tok_growth_cfg (s : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((([1] : List (Fin 2)) ^ 2) +>
    ((0 : Fin 2) >> ((0 : Fin 2) >> encLeft [(s,0)])))
      {{D}}> ((1 : Fin 2) >> ((0 : Fin 2) >> default))

/-- Exact configuration emitted by the original source after 36 steps from T(s). -/
def s3_tok_growth_cycle_cfg (s : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
    (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
    (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
    (1 : Fin 2) >> encLeft [(s,0)])
      {{D}}> ((1 : Fin 2) >> default)

/-- The source path is 36 steps, but its endpoint is the corrected cycle candidate,
not T(s+5). -/
theorem s3_tok_growth_36_to_cycle (s : ℕ) :
    ReachesPlus target (s3_tok_growth_cfg s) (s3_tok_growth_cycle_cfg s) := by
  unfold s3_tok_growth_cfg s3_tok_growth_cycle_cfg
  iterate 36 tstep

/-- Candidate 4-step lasso from the exact post-36 configuration. -/
theorem s3_tok_growth_cycle4 (s : ℕ) :
    ReachesPlus target (s3_tok_growth_cycle_cfg s) (s3_tok_growth_cycle_cfg s) := by
  unfold s3_tok_growth_cycle_cfg
  iterate 4 tstep

#print axioms s3_tok_growth_36_to_cycle
#print axioms s3_tok_growth_cycle4
