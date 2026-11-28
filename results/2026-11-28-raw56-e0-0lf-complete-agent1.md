# Raw56 E0=0LF: complete source-certified Cover at weighted bound 40,000

**Date:** 28 November 2026  
**Scope:** local Raw56 child theorem; this is not a proof of the BB(6) upper bound.

Consider the Raw56 E1=0LE child
```
1RB---_1RC---_0RD---_1LD1LE_0LF0LE_------
```
under the repository's standard two-symbol, six-state conventions. The original
canonical checker now proves a complete
`Cover (WeightedBound 40000)` for this entire partial machine.

## Exact canonical reduction

The pinned canonical search has exactly **2,046** open leaves in this child.
The original-source conditional closure accepted in GitHub Actions run
**46112103663** discharges **2,045** of them and leaves one literal residual,
global Raw56 E1=0LE open index **3613**:

```
1RB---_1RC0RE_0RD0RF_1LD1LE_0LF0LE_1RA0LB
```

The conditional theorem is
`BB6.Agent1Raw56.LE0LFPartial.sound1`. Its proof uses the original canonical
checker and source-level FAR, finite-stack, and finite late-run certificates.

## Final residual: periodic-stack fixed point

The remaining leaf admits a finite two-stack fixed point. Discovery uses the
periodic word `111110` on both stack summaries with parameters

```
k = 30
group = ("111110", c = 3, m = 3)
```

on each side. The untrusted saturation has **45,865 reachable joint states**
and **2,426 stack edges**. An independent observational quotient followed by a
fresh fixed-point re-saturation reduces this to **9,210 joint states** and
**785 stack edges**.

The emitted certificate is checked by the unchanged
`im-results/agent32-raw59/FastBiDFA.lean` kernel checker against the literal
partial transition table. The exported theorem is

```
BB6.Agent1Raw56.LE0LFMotif3613.M3613.never
```

and the complete child theorem is

```
BB6.Agent1Raw56.LE0LFFull.cover :
  Cover (WeightedBound 40000) BB6.Agent1Raw56.LE0LFPartial.p
```

with quotient-facing helper
`BB6.Agent1Raw56.LE0LFFull.all_quotient`.

## Source acceptance

GitHub Actions run **46122584096** succeeds under Lean **4.36.0-rc2** and
uploads artifact **15253379791**, named
`raw56-le0LF-complete-source-accepted`, with artifact digest

```
sha256:1fd2148fabd3e3b38cea4da83afd3d80a9268d16c6b62301e9c12d43a90457bb
```

The generated leaf source has SHA-256

```
1aada4a75c14b66b818872abcad2ff9b85a4ed2e011ccaa8c41a40e84fe7d9f9
```

The axiom gate reports only `propext`, `Classical.choice`, and
`Quot.sound`; neither `sorryAx` nor `native_decide` is admitted.

## Reproduction

The exact generator is
`im-results/agent1-raw56/le/prove_motif_3613.py`; the final composition is
`im-results/agent1-raw56/le/Raw56LE0LFFull.lean`. The manual source gate is
`.github/workflows/agent1-raw56-le-0lf-complete.yml`.

This closes one of the previously unresolved E0 siblings of Raw56 E1=0LE.
The larger E1=0LE parent still requires the other residual siblings to be
closed; this local theorem alone does not establish a global BB(6) upper bound.
