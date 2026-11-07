# #429: original physical C/01 gate requires an earlier left-writing source row

**Scope (7 November 2026).** Intermediate original-blank-root causal reduction for the complete six-state two-symbol holdout `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`. This does **not** decide #429 or BB(6), and it does not by itself improve any global or machine-score bound. The stronger-looking all-time record-right invariant remains unproved.

## New reusable theorem

[LastLeftWrite.lean](LastLeftWrite.lean) proves for any six-state machine `m` in the actual bi-infinite physical tape semantics of `BB6Coverage.Frontier`: if `run m n blank = some c` and a marked tape cell `y` lies strictly to the right of `c.head`, then **some earlier successful step** `k<n` scanned precisely `y` and executed a transition writing `true` while moving **left**. The witness includes a real earlier configuration `d`, the actual instruction `t`, and `m (readSlot d) = some t`.

The proof inducts on all successful raw execution steps. At the last step, either the scanned cell is `y` (the claimed write and leftward movement are forced by the marked symbol and final head position), or the marked cell is unchanged and stays to the right of the predecessor's head; recurse. It uses no assumption about the transition table besides deterministic binary writes and unit left/right head moves. The earlier [Agent 32 marked-cell theorem](../agent32-429-raw-parent/FreshCell.lean) identified an earlier scan of any marked cell but did not characterize the writing instruction or its direction.

## #429 specialization

[BB429LastWriter.lean](BB429LastWriter.lean) proves by exhaustive inspection of the unchanged, fully fixed [physical table](../agent1-429-physical-frontier/BB429PhysicalFrontier.lean) that the **only** leftward write-one source rows are `D/0`, `E/1`, and `F/1`. Therefore every genuine blank-origin state `C` scanning `0` with `1` immediately to its right has a **prior authentic visit to that right-hand coordinate with one of these three read slots**. This is a temporal physical-tape dependency, not an abstract accelerated-predecessor statement.

Agent 32's independently source-checked [all-time raw halting biconditional](../agent32-429-raw-parent/README.md) says exactly that #429 halts iff its true blank trajectory reaches such a `C/01` configuration. Combining it with this module implies that any actual halt requires an earlier `D/0`, `E/1`, or `F/1` left-marking event at the later fatal C-head+1 coordinate. The conjunction has **no** all-time exclusion of these three predecessor rows. Their prior occurrence is necessary, never asserted sufficient.

## Reproducibility and evidence boundary

- The generic Lean theorem `right_marked_has_left_writer`, source row classification `left_marking_source` and true-root consequence `marked_C_right_requires_left_mark` all compiled locally under Lean **4.36.0-rc2**, with reported axioms `[propext, Quot.sound]`. The local physical-table interface was a faithful short reconstruction of the checked-in eleven transitions, so this local check alone is **not** an unchanged-repository-source CI result.
- The [dedicated manual-only CI workflow](../../.github/workflows/agent18-429-lastwriter.yml) imports the real, unchanged `Frontier`, original physical `BB429PhysicalFrontier`, and existing Agent 32 B/001 and C/01 proofs before compiling both new modules. The first invocation is [GitHub Actions 42336857022](https://github.com/FlareZ123/bb6/actions/runs/42336857022). **Its final status must be independently checked** before citing successful native-source compilation; the workflow rejects `sorryAx`.
- There are no new rules added to the raw machine, no numerical finite-search assumptions, no synthetic initial tapes, and no `sorry` in the two new modules.

## Exact missing obligation

A decisive outcome needs a uniform invariant forbidding marked-right `C/01` on **all actual** blank-origin configurations, or an explicit authentic halt. The new writer classification narrows a possible backward history but allows all three marking instructions to occur in genuine runs. The earlier finite observation that C/0 is always at the running rightmost coordinate is **not** a theorem, so it cannot be used as the missing step.

A useful next experiment is an all-time classification of configurations after each one of the three left-writing rows: which of their marked cells can later be approached from their immediate left in state C scanning zero? Such a proof must include the full physical head/tape history across accelerated `J(u,w)` exceptional returns. Prior necessary arithmetic gates in [Agent 1's inverse sieve](../agent1-429-262144-sieve/README.md) and [Agent 6's original halting criterion](../agent6-harmonic429/README.md) are substantially stronger in parameter density; this note makes no novelty or machine-decision claim over them.
