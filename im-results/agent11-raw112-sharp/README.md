# Raw112 sharp weighted maximum — candidate 91,503, Lean acceptance in progress

## Source-accepted foundation

The complete six-hole parent

```text
1RB---_1RC---_0RD---_1LD1RE_---1LC_------
```

has an original-source Lean `Cover (WeightedBound 100000)` accepted in [CI 46146501930](https://github.com/FlareZ123/bb6/actions/runs/46146501930), artifact 15263639929, 2,992 authenticated reused imports. The original `PartialAudit` contains 25,004 split nodes, 446,232 cycle certificates and 115,572 terminal first-hole queries, with **two fully closed nonhalting residuals**. The bound 100,000 was deliberately generous and is not asserted to be sharp.

The independent generic [`PartialWeightExact.lean`](../agent11-partial-weight/PartialWeightExact.lean) source proof is now *accepted* in [run 46146755553](https://github.com/FlareZ123/bb6/actions/runs/46146755553), extending exact weight-only checks to partial audits. Because Raw112's two residuals are nonhalting for every completion, they satisfy `WeightedBound B` for **every** natural B, providing precisely the missing residual hypotheses. [`Raw112Reweight.lean`](Raw112Reweight.lean) instantiates that exact necessary-and-sufficient criterion for the complete Raw112 parent.

## Reproducible candidate, not yet a theorem

The source-pinned standalone [discovery CI 46147673209](https://github.com/FlareZ123/bb6/actions/runs/46147673209), using [`analyze_query_weights.py`](analyze_query_weights.py), independently parses the original `inductive-generators.tar.xz` hard leaf source bank, whose `hard.txt` SHA-256 is `23805b6953da558d904471078a742f87767945ec835afd5ebe602fbb68d32f69`. It exactly enumerates simple zero-preserving control paths from each of the six special late first-query audit leaves. The weight contribution is `first_hole_steps + maxIncomingBlankDelay + 1`. Results:

| Hard leaf | First-hole steps | Maximum zero-prefix delay | Weighted score |
| --- | ---: | ---: | ---: |
| 11 | 2,062 | 1 | 2,064 |
| 12 | 2,327 | 1 | 2,329 |
| 13 | 4,135 | 1 | 4,137 |
| 16 | 1,211 | 1 | 1,213 |
| **22** | **91,502** | **0** | **91,503** |
| 98 | 2,527 | 0 | 2,528 |

Original `enumerate_fast.cpp` has `L=1000`, so all other first-query leaves have `n≤1000` and maximum possible initial zero-write delay five; these have weighted score ≤1006. The other initially open leaves are now certified nonhalting by original-source proofs and do not contribute any halting score.

The winning **halting completion candidate**, obtained by setting its sole unassigned A/1 slot to a halt transition, is

```text
1RBHHH_1RC0LB_0RD0LB_1LD1RE_0RF1LC_1RA0LB
```

The corresponding one-hole table (hard index 22) is

```text
1RB---_1RC0LB_0RD0LB_1LD1RE_0RF1LC_1RA0LB
```

A first-hole run of 91,502 ordinary steps and zero incoming blank delay would give weighted score 91,503. The arithmetic candidate is deterministic and reproducible, but a discovered number is **not** a Lean theorem or a certificate of a halting trace. The source already has checked `.last 91502 (0,true)` in its nested `PartialAudit`.

## Decisive mathematical acceptance edge

[`Raw112SharpBound.lean`](Raw112SharpBound.lean) demands **two kernel proofs** over the full source-accepted audit:

```lean
partialWeights 91503 parent tree = true
partialWeights 91502 parent tree = false
```

Combining these with the accepted generic iff and the independent two nonhalting residual Covers gives

```lean
(∀ m, compatible parent m → WeightedBound B m) ↔ 91503 ≤ B
```

The same formal argument derives an actual compatible halting attaining completion by contradiction: if no machine attained 91,503, the 91,503 bound would imply a 91,502 bound, contradicting necessity. This is stronger than showing merely a candidate run.

The original-source parent-reuse audit is [`.github/workflows/agent11-raw112-reweight.yml`](../../.github/workflows/agent11-raw112-reweight.yml), [run 46148052814](https://github.com/FlareZ123/bb6/actions/runs/46148052814), initial in progress 13:09 UTC, Lean 4.36.0-rc2. It downloads the *source-accepted* 1.16-GB parent artifact and checks all exact source identities before compiling the new proofs. Do **not** publish 91,503 as a result, or update the parent theorem's bound in `results/`, unless this or an equivalent original-source CI pass proves the precise theorem and standard-axiom profile.

The general arithmetic [`PartialWeightScore.lean`](../agent11-partial-weight/PartialWeightScore.lean) is a separate proposed source-checked fold proof that can provide the exact score without traversing `partialWeights` twice; treat this as an optional fallback if direct `by decide` is too expensive.

BB(6) itself remains unsolved even if the Raw112 local exact value passes. The authenticated global Canonical39 roster still requires integrating Raw47 and Raw112 as separate accepted edges.
