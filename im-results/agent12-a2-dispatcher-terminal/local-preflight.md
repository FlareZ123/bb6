# Isolated Lean preflight: A2 BinDec reparameterization

**Outcome:** the A2 arithmetic/list proof module compiled successfully in an isolated Lean 4.36.0-rc2 environment. The actual repository import closure and the complete root-to-terminal composition have not yet been compiled.

## Environment

- Reconstructed Lean 4.36.0-rc2 from the two uploaded split archive parts.
- The supplied zip extraction produced `lean-4.36.0-rc2-linux.tar.zst`; extracted that tar.zst into `/tmp/lean`.
- `lean --version` reported Lean 4.36.0-rc2.

## What was compiled

A temporary local `S1Encoder.lean` module was built from the relevant definitions and theorem interfaces copied from the repository's `im-results/agent8-s1-encoder/S1Encoder.lean`:

- `d0`, `d1`, `markerWord`, `lh`;
- `d0pow`, `d1pow`;
- `binaryCounterFuel`, `binDec`;
- `binDec_even`, `binDec_odd`;
- `binDec_sub_one_carryPrefix`, `binDec_zero`.

That isolated module compiled to `S1Encoder.olean`. Then the exact code now committed as `A2Reparameterization.lean` was compiled with `LEAN_PATH=/tmp/a2lean`. Lean exited with return code 0 and no diagnostics.

The checked theorems are:
- `binDec_max`;
- `binDec_addFour_subSeven`;
- `binDec_lowCarry`;
- `a2Tail_eq`;
- `a2FullLeftFacing_eq`.

In particular, the full left-facing equality is kernel-checked against the copied S1 encoder definitions, including the two carry-prefix identities needed to rewrite the authentic A=2 q4Tail residual into the canonical S1 configuration.

## Scope limitation

This is an isolated arithmetic preflight, not a compile of the repository's actual `S1Encoder` import closure. The temporary module copied the relevant definitions and theorem interfaces, so a follow-up local compile against the real project files is still required. No q4Tail root run, counted-drain composition, 24-class dispatcher composition, terminal bridge composition, or BB(6) claim was verified here.
