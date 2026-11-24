/-!
WITHDRAWN 2026-11-24: universal nonhalting claim is false.
See ../agent48-token-return-correction/README.md. Historical draft only.
Do not dispatch this proof target or use these declarations as accepted lemmas.
-/

/-!
Original-source Lean study of the residual-one token family.

The proposed 36-step map T(s) -> T(s+5) is false. The first two exact
36-step segments are kernel-accepted:
  T(s) -> D1-intermediate -> C1-state.
The next source replay exposes an exact B1 intermediate after 36 further
steps. A further 36-step segment is being tested toward the E-state target.
No cycle or nonhalting claim is made here.

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

/-- Exact B-state after another 36 primitive steps from C1. -/
def s3_tok_growth_B1_cfg (s : ℕ) : Cfg (Fin 2) (Fin 6) :=
  encLeft [(s,0)] <{{B}}
    ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
      (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
      (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
      (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
      (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
      (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> default)

/-- Candidate E-state reached after 36 further primitive steps, for positive s. -/
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

/-- Third 36-step segment, from C1 to the exact B1 intermediate. -/
theorem s3_tok_growth_36_C1_to_B1 (s : ℕ) :
    ReachesPlus target (s3_tok_growth_C1_cfg s) (s3_tok_growth_B1_cfg s) := by
  unfold s3_tok_growth_C1_cfg s3_tok_growth_B1_cfg
  iterate 36 tstep
  exact ⟨0, rfl⟩

/-- Fourth 36-step segment, from B1 toward the E-state target. -/
theorem s3_tok_growth_36_B1_to_E0 (s : ℕ) (hs : 0 < s) :
    ReachesPlus target (s3_tok_growth_B1_cfg s) (s3_tok_growth_E0_cfg (s-1)) := by
  unfold s3_tok_growth_B1_cfg s3_tok_growth_E0_cfg
  texecute 36

/-- T(s) reaches the exact C1 state after 72 primitive steps. -/
theorem s3_tok_growth_to_C1 (s : ℕ) :
    ReachesPlus target (s3_tok_growth_cfg s) (s3_tok_growth_C1_cfg s) :=
  ReachesPlus.trans (s3_tok_growth_36_to_intermediate s)
    (s3_tok_growth_36_to_C1 s)

/-- T(s), s>0, reaches the E-state target after four 36-step segments. -/
theorem s3_tok_growth_to_E0 (s : ℕ) (hs : 0 < s) :
    ReachesPlus target (s3_tok_growth_cfg s) (s3_tok_growth_E0_cfg (s-1)) :=
  ReachesPlus.trans (s3_tok_growth_to_C1 s)
    (ReachesPlus.trans (s3_tok_growth_36_C1_to_B1 s)
      (s3_tok_growth_36_B1_to_E0 s hs))

#print axioms s3_tok_growth_36_to_intermediate
#print axioms s3_tok_growth_36_to_C1
#print axioms s3_tok_growth_36_C1_to_B1
#print axioms s3_tok_growth_36_B1_to_E0
#print axioms s3_tok_growth_to_C1
#print axioms s3_tok_growth_to_E0
