# #303 exact blank-root halting precursor, source-linked proof candidate

**Research state (6 November 2026): formal proof against a source-shaped local accelerator; unchanged-original Cryptids verification dispatched and pending.** This is a provenance upgrade of Agent 21's already established mathematical gateway, plus a direct inductive proof of its explicit two-pattern syntax. It does not establish that the true blank orbit avoids either pattern, decide #303, or determine BB(6).

## Precise theorem and root

The six-state machine is `1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LF---_1LD1LF`. The [original Cryptids machine at pinned commit c86f1586](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/Accelerations/M_1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LFHHH_1LD1LF.lean) has high-level states `E(L,R)`, starting from `E([1],[])`, reached after five raw steps. A zero at the head of `L` makes the next accelerated transition undefined.

The source-referencing `BB303Gate.next_bad_iff` states, for all lists `L,R`, that the next accelerator state has a zero-headed left list exactly when `BadNext L`. The inductive theorem `badNext_shape` converts this Boolean-like condition into the **two exact classes**:

```
L = 3 :: 0 :: tail
L = 1 :: (replicate k 0 ++ 2 :: 0 :: tail), k >= 0
```

The all-time `root_halts_iff_reaches_precursor` asserts that this authentic high-level blank-start run eventually fails **if and only if** some previously genuinely reached state has one of those two dangerous left-list shapes, with an optional list `R`. The equivalence has no simulation cutoff or restriction on tape size. The reverse direction reaches an undefined transition in exactly two accelerated steps from the precursor; the forward direction proves survival by induction while both patterns are avoided.

## Verified boundary, source and reproduction

The [XZ/Base64 Lean source](BB303SourceGate.lean.xz.b64) reconstructs 8,473 UTF-8 bytes with SHA-256 `9e1c1bae8a4800d05e736eb28918409f9e3d39877290baa1c916b51787738a58`. Its definitions of the original `sweepElem`, `sweepRight`, `sweepFL`, `next`, `start` are **imported** from the pinned upstream rather than redeclared. It proves the sweep invariants and the exact two-pattern induction without `sorry` or custom axioms. A local Lean 4.36.0-rc2 test passed using an independently transcribed `UpstreamMock.lean` identical in those definitions; that local test by itself **cannot certify original-source linkage**.

The [manual upstream CI workflow](../../.github/workflows/agent1-303-original-source.yml) clones the exact Cryptids commit, restores Mathlib, builds its unmodified original #303 module, verifies the decoded source hash and compiles the full gate theorem. Consult the run outcome before upgrading the proof's provenance. The theorem audits are included in the file; only standard Lean axioms were reported by the standalone local check.

This adapts and adds a syntactic shape theorem to Agent 21's [original copied-model precursor analysis](../agent21-zero-run303/README.md), which was already Lean-proved in a faithful independent transducer. No external mathematical priority is claimed.

## Remaining decisive question

The real blank-reachable language of **both** zero-run stacks must be proved to exclude the two patterns at every accelerated step, or a genuine blank-root witness must be found. In exploratory 100,000-step exact transducer simulation no halting precursor arose. The left stack exhibited only `0,1,2` internally, with `3,4` only at its head and interior zeros typically surrounded by ones. That empirical language is **not an inductive invariant for all arbitrary right stacks**: synthetic `E([], [3,2])` already breaks a simplistic left-only bound, and `E([4],[])` creates a trailing zero. Thus a proof needs correlated left/right information and treatment of exceptional short stacks. The finite observations are not a nonhalting argument.
