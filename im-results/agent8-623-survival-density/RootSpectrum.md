# #623: an all-time low-third-coordinate spectrum for the authentic blank-root orbit

**Agent 8, 9 November 2026. Intermediate source-connected arithmetic result.** The exact six-state Busy Beaver function remains unresolved. The proof targets the original Cryptids #623 accelerator for
`1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA`, beginning at `D(0,7)`. The complete Lean module is [RootSpectrumSource.lean](RootSpectrumSource.lean).

## The main theorem

Let `T = highLevelNext` and `run(0)=some(D(0,7))`, `run(n+1)=run(n).bind T`, as already defined and source-certified in [Agent49's Parity623Source.lean](../agent49-parity623/Parity623Source.lean). The theorem `run_low_third_spectrum` states for **every natural n**:

```lean
run n = some (.D a d) →
  d = 7 ∨ d = 9 ∨ d = 10 ∨ d = 12 ∨ d = 14 ∨ 23 ≤ d
```

In particular, a surviving authentic return has `d ≥ 7`; none has `d=8,11,13,15,16,17,18,19,20,21,22`. All outputs `0≤d≤6` are also excluded. This is a universal blank-root statement rather than a finite trace finding.

The stronger **one-return** theorem `next_low_third_spectrum` applies to all synthetic as well as authentic source states satisfying `a%2=0` and `d≥7`, whenever their next return succeeds. Under these two assumptions, it establishes the same spectrum for the output third coordinate. A separate `next_forbids_eight` proves the simpler one-step exclusion using only `a%2=0`, without a lower bound on input d.

The five isolated values in the spectrum are genuinely attained by even-first-counter source states with input `d≥7`:

| Input | Output third counter |
|---|---|
| `D(0,8)` | 7 |
| `D(2,8)` | 9 |
| `D(2,7)` | 10 |
| `D(4,7)` | 12 |
| `D(0,7)` | 14 |

These examples show the low spectrum is sharp for the specified broad input domain. They do **not** assert authentic blank-reachability of each synthetic example.

## Proof mechanism

The source return map has seven disjoint cases. New exact symbolic lemmas settle the cases with even first counter `a≤8`, using finite small-digit evaluator identities and direct `drainB` equations. The positive first counter `a≥10` is handled uniformly: `drainB_d3`, already proved against the original source, bounds a completed drain's third counter below by its initial third counter plus three times its block count. In the remaining even-right branch, a new evaluator monotonicity lemma `evalA_third_ge` and a special symbolic `a=10` calculation prove the same needed lower bound. Therefore any successful source transition with even `a≥10` and `d≥7` has output third counter **at least 29**.

The entire one-step proof is then a finite partition on `a=0,2,4,6,8` versus `a≥10`, with exact `d` parity and source branch guards. Induction on `run` uses Agent49's original-source `run_preserves_even` and the new `run_third_ge_seven`. The strengthened spectrum follows directly, with no finite cutoff in n.

## Verification and limits

A standalone faithful copy of the original upstream `evalA`, `drainB`, and `highLevelNext` equations compiled in Lean 4.36.0-rc2 without `sorry`; theorem axiom audits showed only ordinary Lean foundations and two locally declared interfaces standing for the **already source-certified** parent theorems `drainB_d3` and `run_preserves_even`. The committed [source-import module](RootSpectrumSource.lean) replaces those local interfaces with actual imports from the original pinned `google-deepmind/cryptids@c86f15861709b76042998c5211c7b2f83991621b` via Agent8BudgetSource and Agent49ParitySource. The manual [source workflow](../../.github/workflows/agent8-623-third-affine.yml) was extended and dispatched during this run; original-source CI success must be confirmed separately before claiming this new theorem is independently source-certified.

**BB(6) and #623's blank-root halting status remain open.** The spectrum removes infinitely many candidate predecessor configurations with low third counter, but all large third counters are still permitted. Future inverse analysis should intersect possible terminal ancestors and return preimages with this proven root-compatible spectrum, and retain the high-counter digital safety budget for the remaining candidates. Do not promote this intermediate result to `results/` without a stronger research advance and independent novelty assessment.
