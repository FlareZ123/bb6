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


## A computable macro with kernel-proved exact semantics

[SpaceNeedleOddMacroCertified.lean](SpaceNeedleOddMacroCertified.lean) implements a total certified recursive \`splitTwos(n)\`: for every positive n it returns a unique factorization \`n=2^v*u\` with odd positive \`u\`, locally kernel-proved by strong induction. The executable \`oddMacroNext(d)\` takes a single published \`highLevelNext\` call on even d and compresses the **entire maximal odd block** on odd d (where d+1=2^v*u).

The universal theorem \`oddMacroNext_sound_all\` shows, for **every natural counter d**, its returned high-level call count t is positive and exactly \`runHigh t (some (N d))\` equals its returned destination option. No arbitrary invariant or finite simulation assumption appears in this proof. Local Lean 4.36.0-rc2 compilation and \`#print axioms\` checked \`splitTwos_spec\`, \`oddMacroNext_sound\`, \`oddMacroNext_sound_all\`, all with exactly \`[propext, Quot.sound]\` and no sorry. [Source-import candidate](SpaceNeedleOddMacroCertifiedSource.lean) substitutes the original Cryptids import chain; source-CI remains pending runner recovery.

Independent exact-integer test [validate_odd_macro.py](validate_odd_macro.py) replayed the actual blank-seed \`N1\` for **100,000 original high-level calls** and compared each macro destination with the fully unaccelerated exact high-level successor. All 75,221 macro calls agreed and consumed exactly 100,000 original high-level calls (24.779% fewer high-level dispatcher calls). Longest consecutive odd block length was 16. Final counter length was 93,880 bits; checkpoint digest \`652153a408f55ea94900411554a7d1be4ff1dea351c54abb8e3e285b02476dd2\`. This is finite performance/semantic evidence, not a new halting lower bound or proof of nonhalting. The direct symbolic Lean refinement gives all-input correctness beyond the finite cross-check.
