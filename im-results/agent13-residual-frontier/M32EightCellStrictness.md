# M32 high-gateway quotient: strict eight-cell refinement

**Date:** 2026-11-23  
**Status:** Lean 4.36.0-rc2 kernel-checked; CI run [45227845153](https://github.com/FlareZ123/bb6/actions/runs/45227845153) passed.

## Exact result

Let
[
k=2^{2m+2}(j+3)-(j+3m+5).
]

For every (j,minmathbb N) satisfying
[
jge3,qquad mge2,qquad
jequiv0pmod4,qquad
mequiv3j+13pmod{32},
]
the Lean theorem `m32_eight_cell_strict` proves
[
operatorname{highAllowed}(j,m)
quadlandquad

egoperatorname{highAllowedM32}(j,m).
]

The eight residue pairs modulo 32 are
[
(0,13),(4,25),(8,5),(12,17),
(16,29),(20,9),(24,21),(28,1).
]
The statement is uniform over every lift of these residue pairs satisfying the displayed lower bounds. Thus it identifies eight infinite parameter families, not eight isolated test points.

## Why the previous sieve admits them

Write (D=j+3m+3) and (P=2^{2m+2}).

- The residue relation gives (mequiv1pmod4), hence (Dequiv2pmod4) and (v_2(D)=1). The older dyadic gate requires valuation at least two, so it cannot fire.
- (j+9m+14equiv3pmod4), so the fast-depth candidate is odd and its 2-adic valuation is zero.
- The stopping value satisfies (kequiv0pmod4), hence (k+2equiv2pmod4) and (v_2(k+2)=1). The late-depth gate, which requires valuation at least two, cannot fire.
- The finite joint, C58, and diagonal exclusions are incompatible with (jequiv0pmod4), (mequiv1pmod4), and the exact modulo-32 relation.
- The affine normalizer is inert: (kge8), (kequiv0pmod4), and ((2j+3+k)equiv3pmod4).
- The six-forced inverse exclusion is false throughout this family; the proof uses (2j+3equiv3pmod8), (kequiv4pmod8), and ((2j+3+k)equiv7pmod8).

The M32 source quotient nevertheless rejects all eight cells. Membership in the finite M32 forbidden-pair certificate is obtained from the kernel-checked `CCert.newHighPairs_excluded` theorem.

## Source chain and verification

- [`CThreeSixM32Integration.lean`](CThreeSixM32Integration.lean) combines the original CThreeSix criterion with Agent 4's source-connected M32 exclusion and proves `blank_halts_iff_six_m32`.
- [`M32EightCellStrictness.lean`](M32EightCellStrictness.lean) proves `prior_high_allowed_eight` and `m32_eight_cell_strict`.
- [Agent 4's `HighSource.lean`](../agent43-c-quotient-kernel/HighSource.lean) provides the generic original-source theorem `high32_forbidden_source`; [`M32SectionEmbedding.lean`](../agent15-c-halting/M32SectionEmbedding.lean) connects the quotient section to the original CLine transitions.
- [CI workflow](../../.github/workflows/agent4-c-m32-high.yml) regenerates the eight-shard certificate artifacts, compiles the 232-module dependency closure, and kernel-checks the integration and strictness modules.

## Boundary

This is a stronger necessary high-gateway exclusion, not a complete Machine C blank-root decision. The integrated equivalence still has unbounded parameter quantifiers and an unresolved root decision. It does not determine (S(6)) or (Sigma(6)).
