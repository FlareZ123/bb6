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

## Parent integration: exact 14-to-8 E1=0LE frontier

The completed 0LF child is consumed together with the five previously accepted
complete E0 children (0RB, 0RC, 0LB, 1LA, 1RA) in

```
BB6.Agent1Raw56E1LE.sound8_closed
```

GitHub Actions run **46123625812** source-accepts this theorem and uploads
artifact **15255001408**, `raw56-le-six-source-accepted`, with digest

```
sha256:4ef87b64480b7765229c8fc5c25a975fe0cf8f15d9fbd087dd9f0c96049f33b2
```

The theorem says that every full machine compatible with the Raw56 E1=0LE
parent either satisfies `WeightedBound 40000` or extends one of exactly
**eight** residual E0 children. The remaining labels are
`0LA, 0RA, 0RF, 1LB, 1LF, 1RB, 1RC, 1RF`. The source gate reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## Further parent refinement: collapse E0=1LF to one exact residual

The E0=1LF child has **1,307** canonical leaves. Original-source run
**46123920848** proves `BB6.Agent1Raw56.LE1LFPartial.sound1`, discharging
**1,306** of them and leaving exactly global E1=0LE leaf **17557**:

```
1RB1LA_1RC1RB_0RD0RC_1LD1LE_1LF0LE_0LA---
```

The accepted artifact is **15255208881**,
`raw56-le1LF-partial1-source-accepted`, digest

```
sha256:c4582b4a82b22f7a4b65aecc631521504af2795ec927b8f5edbc78436e193836
```

The resulting parent theorem
`BB6.Agent1Raw56E1LE.sound7_plus_17557` is source accepted in run
**46125056711**, artifact **15255367500**, digest

```
sha256:467f9b1184dc1220e719230b9694897268b31e25dfa44590dc411528a5ef4fec
```

It reduces the Raw56 E1=0LE parent to `WeightedBound 40000`, one of exactly
**seven** remaining whole E0 siblings, or compatibility with the one explicit
partial machine 17557. Its axiom profile is
`[propext, Classical.choice, Quot.sound]`.

Leaf 17557 is not claimed nonhalting here. The intermediate files
`analyze_17557_dyadic.py`, `analyze_17557_renorm.py`, and
`17557-triad-rewrite.md` isolate a dyadic checkpoint family, a ternary
substitution `A→ABA, B→BBA`, and a level-renormalization conjugacy as the
remaining proof target.

## Reproduction

The exact generator is
`im-results/agent1-raw56/le/prove_motif_3613.py`; the final composition is
`im-results/agent1-raw56/le/Raw56LE0LFFull.lean`. The manual source gate is
`.github/workflows/agent1-raw56-le-0lf-complete.yml`.

This closes one previously unresolved E0 sibling and sharpens the Raw56
E1=0LE parent from its former 14-to-9 frontier to the source-certified
14-to-8 frontier above. The eight residual siblings and other Raw56 branches
still prevent a complete parent Cover; these results do not establish a
global BB(6) upper bound.
