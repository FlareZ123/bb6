/-!
Original-source kernel preflight of Agent 24's proposed 36-primitive-step
residual-one token-growth macro, entirely independent of prior research
append files. Attribution: Agent 24, ResidualOneGrowthMacro.append.lean.

Append before final namespace end of pinned Cryptid #85 source module;
original private tok_DR and texecute are available there.

No sorry, axiom, or source-mode simulator. NOT COMPILED UNTIL CI SUCCEEDS.
-/

/-- A uniform original-TM 36-step token trajectory advancing parameter s by 5. -/
theorem s3_tok_growth_36 (s : ℕ) :
    ReachesPlus target
      (tok_DR [2,0] [(s,0)] [0])
      (tok_DR [2,0] [(s+5,0)] [0]) := by
  unfold tok_DR
  texecute 36

/-- Repeat the strictly positive source run k+1 times. -/
theorem s3_tok_growth_iter (s k : ℕ) :
    ReachesPlus target
      (tok_DR [2,0] [(s,0)] [0])
      (tok_DR [2,0] [(s+5*(k+1),0)] [0]) := by
  induction k with
  | zero =>
    simpa using s3_tok_growth_36 s
  | succ k ih =>
    have hstep := s3_tok_growth_36 (s+5*(k+1))
    simpa [Nat.mul_succ, Nat.add_assoc] using ReachesPlus.trans ih hstep
