/-!
Source-local append theorem for the residual-one growth macro.
Append this file inside the pinned source module
M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA, after its local
`tstep`/`texecute` macros and private `tok_DR` definition.

This is intentionally a single direct kernel proof over the actual source
step function. It does not use the generic existential
`tok_DR_2_0_closed` theorem.
-/

private theorem agent24_tok_DR_growth_step (s : ℕ) :
    (tok_DR [2,0] [(s,0)] [0]) [target]⊢⁺
      (tok_DR [2,0] [(s+5,0)] [0]) := by
  unfold tok_DR
  texecute 36
