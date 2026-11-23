/-!
Original-source Lean study of the residual-one token family.

The proposed 36-step map T(s) -> T(s+5) is false. The exact original-source
trajectory has a 36-step D-state intermediate, then a 36-step C-state, then
a further 36-step transition to an E-state carrying a fixed alternating
right word and a unary left parameter. The first two segments are already
kernel-accepted; the third segment is the current preflight target.

Append before the final namespace end of the pinned Cryptid #85 source
module; original private tok_DR and tstep/texecute macros are available.
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

/-- Exact C-state after another 36 primitive steps. -/
def s3_tok_growth_C1_cfg (s : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
    (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
    (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
    (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
    encLeft [(s,0)])
      {{C}}> ((1 : Fin 2) >> default)

/-- Exact E-state reached after 36 more primitive steps, for positive s. -/
def s3_tok_growth_E0_cfg (m : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((0 : Fin 2) >> encLeft [(m,0)])
      {{E}}> ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
        (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
        (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
        (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
        (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
        (1 : Fin 2) >> (1 : Fin 2) >> default)

/-- First 36-step segment, from T(s) to the exact intermediate D-state. -/
theorem s3_tok_growth_36_to_intermediate (s : ℕ) :
    ReachesPlus target (s3_tok_growth_cfg s) (s3_tok_growth_intermediate_cfg s) := by
  unfold s3_tok_growth_cfg s3_tok_growth_intermediate_cfg
  iterate 36 tstep
  exact ⟨0, rfl⟩

/-- Second 36-step segment, from the intermediate D-state to C on symbol 1. -/
theorem s3_tok_growth_36_to_C1 (s : ℕ) :
    ReachesPlus target (s3_tok_growth_intermediate_cfg s) (s3_tok_growth_C1_cfg s) := by
  unfold s3_tok_growth_intermediate_cfg s3_tok_growth_C1_cfg
  iterate 36 tstep
  exact ⟨0, rfl⟩

/-- The token state T(s) reaches the C1 configuration after 72 primitive steps. -/
theorem s3_tok_growth_to_C1 (s : ℕ) :
    ReachesPlus target (s3_tok_growth_cfg s) (s3_tok_growth_C1_cfg s) :=
  ReachesPlus.trans (s3_tok_growth_36_to_intermediate s)
    (s3_tok_growth_36_to_C1 s)

/-- From C1, the next 36 source steps expose an E-state with unary left suffix. -/
theorem s3_tok_growth_C1_to_E0 (s : ℕ) (hs : 0 < s) :
    ReachesPlus target (s3_tok_growth_C1_cfg s) (s3_tok_growth_E0_cfg (s-1)) := by
  unfold s3_tok_growth_C1_cfg s3_tok_growth_E0_cfg
  texecute 36

/-- Every T(s), s>0, reaches the E-state after 108 primitive steps. -/
theorem s3_tok_growth_to_E0 (s : ℕ) (hs : 0 < s) :
    ReachesPlus target (s3_tok_growth_cfg s) (s3_tok_growth_E0_cfg (s-1)) :=
  ReachesPlus.trans (s3_tok_growth_to_C1 s) (s3_tok_growth_C1_to_E0 s hs)

#print axioms s3_tok_growth_36_to_intermediate
#print axioms s3_tok_growth_36_to_C1
#print axioms s3_tok_growth_to_C1
#print axioms s3_tok_growth_C1_to_E0
#print axioms s3_tok_growth_to_E0
