# Strict-growth certificates for two BB(6) holdout accelerations

**Status: intermediate results.** These theorems do not prove that either original machine halts or runs forever. They are stored in `im-results/` accordingly.

## Source transitions

The transitions in [RankCertificate.lean](./RankCertificate.lean) reproduce the `next` definitions in two independently established, Lean-certified acceleration modules from Google DeepMind's [Cryptids](https://github.com/google-deepmind/cryptids) repository:

1. **Machine A** `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`, originally nicknamed *The Sheep Machine*. [Upstream Lean module](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_HHH1LE.lean). Upstream initial counter state `P(0,2)`; halting counter states have `m=1`; `nextA` is its transition function after replacing the constructor `P` by a pair.

2. **Machine B** `1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE`. [Upstream Lean module](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_HHH1RE.lean). Upstream initial counter state `A(3,0,0)`; halting counter states have `a=b=0`; `nextB` is its transition function after replacing constructor `A` by a triple.

The upstream files contain the formal proofs `is_valid_acceleration` and `isHalt_iff_acceleration`. This standalone file proves properties of exact copies of the published accelerated maps. It is not imported directly into Cryptids, so the correspondence is established by inspection, rather than by an additional kernel-checked bridge.

## New intermediate observations

For every `nextA s = some s'`, the integer potential `m+k` strictly increases. For every `nextB s = some s'`, the potential `a+b+c` strictly increases. Lean proves these universally for all natural counter inputs, rather than for an experimental prefix.

The generic theorem `rank_growth` proves that a surviving `n`-step accelerated trajectory increases its initial potential by **at least `n`**. Consequently:

- The Sheep Machine has `m+k ≥ n+2` after any `n` surviving macro steps, starting at `P(0,2)`.
- Machine B has `a+b+c ≥ n+3` after any `n` surviving macro steps, starting at `A(3,0,0)`.
- No surviving accelerated path can revisit an earlier counter state. **Conditionally**, if the corresponding original TM never halts, its encoded macro-configuration footprint is unbounded. The Sheep encoding contains precisely `m+k+1` one-bits; the second contains `a+b+2(c+1)` one-bits.

These are escape-to-infinity certificates that rule out finite macro-state cycles. They leave open whether the paths enter their designated halting states.

## Verification

Run Lean **4.36.0-rc2** directly on `RankCertificate.lean`; it imports only `Lean.Elab.Tactic.Omega`, with no Mathlib or upstream Cryptids dependency. The local compilation exited with status 0.

Follow-up work: connect these certificates to the original Cryptids modules through a Lean import, and investigate whether stronger modular/inequality invariants can exclude the halting sets. A rank potential alone does not do so.
