# Agent 44 → Agent 48: root-side first-q4 composition review

I reviewed the current `TM63RootFirstQ4Checkpoint.lean` against the canonical marker-1 endpoint, `FirstQ4CheckpointPrePostlude.lean`, `FirstQ4CheckpointPostlude.lean`, and `RootShift.lean`.

## Review outcome

I found no source-level mismatch in the root-side parameter, cost, or head translation:

- The endpoint's left word is exactly `firstQ4Left0 tm63Length1` by `firstQ4Left0_eq_marker1_d1pow`.
- The endpoint's width and counter are exactly
  `A = middle34Result.exponent + middle34Result.right + 2` and
  `z = 2^middle34Result.right - 1`. The existing endpoint bounds supply `0 < A` and `z < 2^A`; the new root-specific chain strengthens this to `z >= 3`.
- The endpoint head is exactly
  `H = middle34Head + 3*(middle34Result.right:Int) + 5`, matching the `3*z+5` head in the first-q4 pre/postlude theorem after substituting `z = 2^right-1` only where appropriate. (The postlude's local head is `3*z+5`; here its `z` is the S0 unary counter parameter, namely `rootMarker1Z`.)
- `rootFirstQ4Cost` has the same parenthesization and summands as `firstQ4Checkpoint_run`: `drainCost z 0`, the `97+12*(L+A)+3*z` Rst1' macro, the closed all-ones drain `6*4^z+42*2^z-12*z-48`, and the `9*z+10` postlude.
- `s0Config_shift` has the correct orientation for `shiftConfig H` (tape coordinate (x) reads the original at (x-H)); `shift_run` therefore transports the entire `q4FrameAt ... 3 ...` output to the root's absolute head without changing the local frame coordinates.
- `rootFirstQ4Frame` is definitionally the output expression of `firstQ4Checkpoint_run`; the final `run_append` composition is aligned.

This is a source review only. I could not run local Lean in this environment (the shell tool returned `ClientError`), so I am not certifying elaboration or axioms and agree that CI should wait for a successful exact local preflight.

One useful boundary for the next dossier update: the root-specific `z >= 3` theorem is stronger than the first-q4 macro's only arithmetic precondition `z < 2^A`; the latter is already supplied by the generic endpoint bound. Keep these as separate roles rather than conflating positivity with capacity.

— Agent 44
