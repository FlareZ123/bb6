# Agent 21: a complete predecessor grammar for holdout #303

**Status (2026-11-03): intermediate only.** This does not decide the machine or BB(6), improve a bound, or establish external novelty. The Lean certificate is compiled locally against a textually faithful copy of the original equations, not independently imported against Cryptids' own Lean definitions.

## Original model

Rooted six-state machine: `1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LF---_1LD1LF`.

[Original DeepMind Cryptids module](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/Accelerations/M_1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LFHHH_1LD1LF.lean), pinned revision `c86f15861709b76042998c5211c7b2f83991621b`, already formally establishes the blank-root acceleration starting from `E([1],[])` after five raw transitions and `isHalt_iff_acceleration`. The new Lean model copies the exact right-mode transducer, left sweep, and one-step equations, using pairs instead of the single `State.E` constructor. This transcribed equality is currently source-inspected rather than kernel-imported.

## New all-input theorem

For a nonhalting accelerated state `E(L,R)`, the next transition produces a state whose left stack begins with zero **if and only if** one of these forms occurs:

```text
L = 3 :: 0 :: tail
L = 1 :: (0 repeated k) ++ 2 :: 0 :: tail, for k >= 0.
```

There is no restriction on `R`. The Lean predicate `BadNext` tests these cases by recursively stripping zeroes from the left-sweep input. With `Good L := L.head? != some 0`, `next_bad_iff` proves:

```text
(∃ s, next (L,R) = some s ∧ ¬ Good s.1) ↔ BadNext L
```

The key proof is a **universal nested induction** on zero-run sizes and the remaining right tape. Every right sweep in mode `br` produces a good output; modes `ar` and `cr` preserve a good left input; and a right sweep beginning with `2` in mode `ar` outputs good regardless of its left stack. The left sweep can therefore generate a leading zero only through its direct `2::0` branch.

The second theorem `root_halts_iff_reaches_precursor` proves an all-time equivalence, for `run 0=some ([1],[])` and `run (n+1)=(run n).bind next`:

```text
(∃ n, run n = none) ↔
(∃ n s, run n = some s ∧ BadNext s.1)
```

A genuine-root nonhalting decision still requires proving that neither pattern is ever visited. A synthetic left stack `[3,0]` demonstrates that these patterns can arise under other initial conditions.

## Evidence and reproduction

The [compressed Lean source](ZeroRunGate.lean.xz.b64) decodes via Python `lzma.decompress(base64.b64decode(...))`. Its exact decoded SHA-256 is `ac2c76e72dbb8c9b94d0056d0becb141964bbc94fbf3ed9bc41a270207f2b1d7`, size 7,205 bytes. Lean 4.36.0-rc2 compiled it without warnings, `sorry`, `admit`, `native_decide`, or custom axioms. Both theorem axiom audits returned `[propext, Classical.choice, Quot.sound]`.

A deterministic direct simulator checked the characterization on 82,026 synthetic stack pairs, and an independent original twelve-rule raw Turing machine interpreter matched 37,492 true E-return states within 300,000 primitive steps. A 200,000-step source acceleration run found no halt. These are finite tests and establish no all-time blank-root survival.

**Next:** construct a correlated blank-origin left/right language that provably excludes the two precursor patterns, or discover a genuine rooted witness; independently recompile against the original Cryptids namespace once CI returns.
