# Space Needle exact maximal odd-block acceleration

**Agent 48, 2026-11-03.** Intermediate source-mirrored locally Lean-kernel-verified reduction; original full-source CI pending, no BB(6) decision.

## Source and theorem

This pertains to the exact DeepMind Cryptids high-level map at `google-deepmind/cryptids@ced8f9f44f67a167d5ecc03e687b048c67926371`, lines 470–501: `HighLevelState.N d`, `scanEven`, `highLevelNext` (see [source mirror](SpaceNeedleSourceMirror.lean)). Starting from any `d=2a−1` with `a≥1`, one high-level transition exists and is exactly `d'=5a−1`. This is the uniform odd branch including the `d=1` special case.

The theorem `BB6.Agent48.SpaceNeedle.odd_block` in [SpaceNeedleOddBlocks.lean](SpaceNeedleOddBlocks.lean) establishes, **for all natural t and positive m**, the exact `t`-call high-level trace

```
N(2^t*m - 1)  --exactly t high-level transitions-->  N(5^t*m - 1).
```

The prefix theorem `odd_block_prefix` checks every `j≤t`: after `j` calls the counter is `2^(t-j)*5^j*m−1`. Hence for `t>0`, every proper prefix is odd; if `m` is odd, the target `5^t*m−1` is even. **Therefore if `m` is odd and `t≥1`, this is the complete maximal consecutive-odd run, with an exact high-level call count `t`.** The Lean proofs explicitly handle natural-number truncation and the `d=1` source special case.

An additional globally quantified theorem `odd_block_terminal_condition` states that if `t≥1,m≥1` and the block output equals terminal counter `2^K−2`, then necessarily `5^t ∣ 2^K−1`. This gives a parametric 5-adic necessary condition for a terminal immediately after a maximal odd block. It does not assert such inputs occur on the actual blank orbit.

## Evidence and interpretation

The five core theorems and `odd_block_terminal_condition` were compiled locally in Lean 4.36.0-rc2, with `#print axioms` reporting exactly `[propext, Quot.sound]` for each (no user axioms, no sorry). The definitions of `scanEven` and `highLevelNext` are source-mirrored from the original pinned Cryptids source, and the proof is fully locally kernel-checkable without Mathlib, placeholder axioms or an Actions runner.

[SpaceNeedleOddBlocksSource.lean](SpaceNeedleOddBlocksSource.lean) imports the original `SpaceNeedleClosed` original-source-associated module rather than the standalone source mirror; this import is not presently CI verified because GitHub Actions executions have been failing before their first step. **Do not misrepresent the mirror as a full original-source import certification.**

Example: `d=23=2^3·3−1` executes `23→59→149→374=5^3·3−1`, with the last even counter. At the real blank entry `d=1`, the formula gives the first high-level step `1→4` using `t=1,m=1`, as required by published source.

This reduction can compress all finite odd runs in Space Needle symbolic simulations and exposes the gateway congruence `2^K≡1 (mod 5^t)`. It is a deterministic symbolic acceleration, **not** a proof of the blank-origin nonhalting question, a primitive Turing machine step count, or a universal BB(6) bound. It is placed under `im-results/` pending practical reuse/novelty assessment.
