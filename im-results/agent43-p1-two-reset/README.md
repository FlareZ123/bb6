# Agent 43: Lean-checked arithmetic core for two-reset P1 wall obstruction

**2026-11-04, intermediate result.** This work independently formalizes the second-reset and final-upper cancellation calculation in Agent 28's [two-reset candidate](../agent28-p1-word-automaton/TWO-RESET-CANDIDATE.md), under **explicit numeric hypotheses**. The original-source `OddCone`/counted-reset theorem is **not** yet proved by this file. P1 nonhalting and BB(6) remain open.

## Main kernel-certified statements

All four modules were locally compiled with **Lean 4.36.0-rc2**. Each terminal `#print axioms` reports a subset of `[propext, Classical.choice, Quot.sound]`; there are no `sorry`, `native_decide`, extra user axioms, or mock dependencies. This is *standalone arithmetic kernel verification*, not a CI run using the original P1 source.

1. **`two_reset_growth`**: for every natural `n≥70`, `4,478,976(n+2)^6 < 6·2^n`. An exact induction uses `(x+1)^6 < 2x^6` for `x≥72`. The base case is kernel-reduced by `decide`.
2. **`two_reset_tail_polynomial_budget`**: if the first reset block satisfies `m₁≤11(n+2)` and `2^m₁≤24(n+2)^3`, second-reset input remainder `M₂>0`, final suffix remainder `N₂>0`, and the exact source-derived dyadic equations hold, then `2^(m₁+l₂+u)≤20,736(n+2)^5` and `m₁+l₂+u≤71(n+2)`. The dyadic cancellation lemma is reproduced verbatim from Agent 28's `OneResetTwoAdic.lean` (as private local theorem) to make the archive standalone.
3. **`two_reset_wall_impossible_from_source_equations`**: under those same hypotheses and the previously source-certified necessary wall inequality `7·2^n ≤ n+4+2^m(3m+2n+4)` (where `m=m₁+l₂+u`), derive `False`. This formalizes the candidate's advertised final polynomial-versus-exponential contradiction without approximating any powers.
4. **`two_reset_defect_positive`**: if `N₁≤n+m₁+1`, `M₂+N₁=2(n+m₁+2)`, `M₂=2^l₂ h`, `l₂≥2`, and `N₂+h=n+m₁+l₂+1`, then `M₂>0`, `N₂>0), and `N₂≤n+m₁+l₂+1`. This discharges the two positivity assumptions when a source-level bridge can supply the displayed defect equations.

## Remaining proof obligation

To turn the conditional arithmetic theorem into an actual zero/one/two-reset P1 exclusion, source-compile an exact two-reset word decomposition of `CountCone` from Agent 28 `OneResetCount.lean`; derive the first intermediate positive defect and terminal suffix equation from unmodified `OddCone`/`UpperTail`/`inverseAt`. Reuse Agent 28's proven one-reset polynomial budget, its defect transport identity, and `two_reset_defect_positive` to supply all hypotheses. This is a specific and consequential source-integration gap; do not present the present result as a new P1 rooted exclusion.

## Reproduction

Decode `two-reset-arithmetic.tar.xz.b64` with base64, confirm binary SHA-256 `fe84098af7576ff7a0c6a128174a969ca5e8ca3bfe86c6880e3c1e2a288f858c`, and extract its four Lean files. Compile `TwoResetGrowth.lean` and `TwoResetTailBudget.lean` into `.olean` dependencies with `LEAN_PATH` pointing at that directory, then compile `TwoResetWall.lean` and `DefectPositive.lean` with Lean 4.36.0-rc2. Read the exact quantified assumptions in the source before applying the statements.

The code is an independent, intentionally limited arithmetic verification of Agent 28's existing candidate, not an independent novelty claim. All materials belong in `im-results/`.

## Source-certified exact two-reset decomposition (2026-11-04)

The new [`TwoResetShape.lean`](TwoResetShape.lean) compiles against the **unchanged original** `OneResetCount.lean`, `OddConeMass`, `UpperTail`, and `inverseAt` source in successful opt-in Lean CI [41759655753](https://github.com/FlareZ123/bb6/actions/runs/41759655753), at source commit `315d945e6010160094533b5431b89eb1aec7e82a`. The final theorem `BB6.Agent43.counted_cone_two_reset_shape` has only `[propext, Classical.choice, Quot.sound]` axioms (and no `sorryAx`). It gives the **exact original-source** decomposition of any `CountCone` history with two positive-depth resets as

`UpperTail ; inverseAt(t₁≥1) ; UpperTail ; inverseAt(t₂≥1) ; UpperTail`.

All intervening zero-depth inverse edges are admitted and not omitted by this decomposition. The proof is entirely structural induction on original `CountCone`. This improves the source alignment of the candidate but **does not yet discharge the arithmetic-bridge hypotheses for those genuine histories**, so no new wall exclusion is claimed.

## Full original-source theorem certified on 2026-11-04

[Manual Lean 4.36.0-rc2 run 41761303380](https://github.com/FlareZ123/bb6/actions/runs/41761303380), job 126349385247 at commit 4e5752bdbaa6307a5b2b43f43793a2fb3b3ccdbb, **success**. Final theorem `BB6.Agent43.source_critical_exact_two_reset_no_wall` is kernel verified against the unchanged original P1 source, with exactly [propext, Classical.choice, Quot.sound] in its Lean axiom audit. For EVERY n>=70 and every genuine critical OddCone history counted as EXACTLY TWO positive-depth inverseAt transitions, the affine wall b=4*(m+n) is impossible. Arbitrary zero-depth transitions are included.

The proof uses original-source [TwoResetShape.lean](TwoResetShape.lean), original Agent28 one-reset budget and defect transport, additional five-file archive [two-reset-bridge.tar.xz.b64](two-reset-bridge.tar.xz.b64) (binary SHA256 321895ed10f828c73551f0af4614094b2ce56440eab17fd9b4c109fc6573793a), and the original four-file arithmetic archive. Both archives have SHA256 checks in [the manual audit workflow](../../.github/workflows/agent43-p1-tworeset-full-source.yml). [SourceInterfaces.lean](SourceInterfaces.lean) contains imports only, with no substitute declarations. The original-source theorem's final axiom list contains no sorryAx.

This upgrades Agent28's existing handwritten conjecture to an authentic source-connected theorem. **The exact BB(6) value, P1 nonhalting, high-cost exits, and three-or-more-reset histories remain open.** External literature-level novelty has not been audited. The optional [ThreeResets.lean](ThreeResets.lean) corollary requires a separate CI result.
