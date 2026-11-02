# Agent 10: Machine B parity-word aperiodicity

Status: **intermediate**, without a holdout decision, new BB(6) bound, or claimed number-theoretic novelty.

Source Lean: [Agent10BParity.lean](./Agent10BParity.lean). The published Machine B scalar acceleration is `G(z) = 3*(z/2)+4+5*(z%2)`. With the shift `x=z+8`, the conjugate map is `T(x)=(3*x+7*(x%2))/2`.

Fully quantified results proved in Lean 4.36.0-rc2:
- `T_pos`: every `x>0` strictly increases under `T`.
- `prefix_div_pow_two`: if `x<=y` and their first n parity bits agree, `2^n` divides `y-x`.
- `all_bits_equal_implies_equal`: an infinite parity word uniquely determines its initial positive-integer state.
- `parity_orbit_aperiodic`: no positive trajectory has eventually periodic parity.
- `B_scalar_bits_aperiodic`: the original G trajectory from 0 is parity-aperiodic.

Lean emitted only `[propext, Quot.sound]` dependencies and no `sorryAx`.

[Agent10BSource.lean](./Agent10BSource.lean) establishes definitional equality with the upstream-derived scalar source `BB6.OneDim.G` and restates the theorem for the source-connected Machine B reduction. The existing manual-only workflow `.github/workflows/agent18-b-bridge.yml` now verifies the complete Lean source chain. Check its latest Actions run before claiming the source-connected CI audit succeeded.

**Important limitation:** Agent 18's exact blank-halting criterion samples parity at sparse, recursively defined indices `scalarA n`. Aperiodicity of the whole itinerary does not establish parity of those samples, so Machine B and BB(6) remain unresolved.

The underlying parity coding is related to classical generalized Collatz parity vectors; originality requires a separate prior-art review. Keep this work under `im-results/`.
