# A source-exact second wedge outside the original B8/M32 exclusion power

**Agent 3, 2026-11-03. Research programme R003, intermediate mathematics.**
Machine C and BB(6) remain undecided. This research isolates an infinite, explicitly parameterized genuinely blank-unreachable family that is *present* in the existing certified B8/M32 abstract reachable graph. Do not infer a complete Machine C verdict.

## Exact original-source inverse result

Let `secNext` be the unchanged original Machine C first-return section map and let `CReach x y` refer to the authentic blank section `(5,1)`.

For **all** naturals `x,y,a,k` satisfying

```
x % 2 = 0
y % 2 = 1
y >= 5
(x+y+1) % 16 = 8
x+y >= 23
```

the complete original-source predecessor equation is

```
secNext(a,k) = some(x,y)
  ↔ x+y = 2*a+5 AND x+3*y = 4*k+9.
```

Every target has exactly one predecessor `a=(x+y-5)/2`, `k=(x+3*y-9)/4`. Proof `BB6.Agent3.odd_seven_parent_iff` in [OddSevenSliver.lean](./OddSevenSliver.lean). It descends directly from the previously source-verified full exact [`section_preimage_all_iff`](./SectionAllInverse.lean) and rules out all unbounded bounce-depth alternatives using exact divisibility.

A new two-dimensional subfamily is

```
T(p,q) = (8p,8p+64q+23),  p,q in Nat.
```

The sole actual predecessor of `T(p,q)` is

```
P(p,q) = (8p+32q+9,8p+48q+15).
```

Every `P(p,q)` lies inside the prior source-certified blank-forbidden region [`OddSliver.lean`](./OddSliver.lean), because the first coordinate is 1 mod8, the second is odd at least five, and their sum is 8 mod16 and at least 24. Consequently `BB6.Agent3.odd_seven_slope_blank_unreachable` proves for **all** p,q,time that the genuine blank orbit never reaches `T(p,q)`.

## Exact relation to the previous M32 quotient

The stronger existing Agent43 B8/M32 abstract reachable graph has 31,570 reachable classes out of 64,000. Its soundness against unmodified original Machine C three-counter semantics is independently source-certified by Agent43's CFull32/bridge formalization. A quotient *absence* proves genuine absence; a quotient *presence* says only that the abstraction is inconclusive.

The independent [source interpreter reproduction](../../tools/agent3_c32_overlap.py), using the unchanged [Agent43 graph oracle](../../tools/agent43_c32_certificate.py), checks that **every** abstract cell representing `T(p,q)` is *present* in that existing quotient, for every parameter p,q (finite residue proof: x has period32 above the base threshold, k residue depends on p mod4, and q disappears mod32). In particular the state `(0,23)` is quotient-admitted, while the original-source inverse theorem gives its single predecessor `(9,15)`, which is genuinely unreachable from blank.

This is a **strict improvement in excluded genuine states over that particular finite quotient**, achieved by one exact predecessor step and the older forbidden-parent lemma. It does not establish external novelty relative to all recent other arithmetic source theorems; that requires independent review.

A related [first wedge dossier](./OddSliver.md) proves other globally forbidden pairs; an overlap audit determined that the first wedge and its previously studied low/high halting subclasses were **already excluded by Agent43's B8/M32 quotient**. They remain useful exact source-inversion lemmas, but yield no additional excluded roots or quotient-forbidden target classes. This distinction corrects earlier interpretations.

## Verification and limitations

The manual original-source Lean 4.36.0-rc2 verifier is [`.github/workflows/agent3-c-bounce-inverse.yml`](../../.github/workflows/agent3-c-bounce-inverse.yml) with input `balanced_only=true`. It compiles the original source `FastSectionDef`, original all-depth inverse theorem, authentic blank-image proof, [`OddSliver.lean`](./OddSliver.lean), and [`OddSevenSliver.lean`](./OddSevenSliver.lean). Axiom audit requires standard Lean axioms only and no `sorryAx`.

The second wedge is an intermediate mathematical structural result. In particular, the infinite `T(p,q)` family is **not claimed to contain a Machine C halting input**, and the present work neither closes a whole stopping family nor determines BB(6). A high-value next problem is whether the exact reverse-wedge mechanism can be transferred to remaining genuine halting-gateway complements rather than reproducing certificates already settled by the finite quotient.
