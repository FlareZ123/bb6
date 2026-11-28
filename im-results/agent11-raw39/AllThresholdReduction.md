# Raw39 all-threshold dominance: the entire first-hole cylinder reduces to 1LE

## Exact mathematical claim

Let
`P = 1RB---_1RC---_0RD---_1LD0RA_------_------` be the residual Raw39 cylinder,
and let `Q = refine P (A,1) (1LE)`. Here `Bound B R` means that every
halting completion of partial table `R` has weighted halting cost at most
`B`, with the first-one halt-query/delay convention of the accepted
`BB6Coverage` library.

**Theorem (all threshold values).** For every natural number `B`,

```
Bound B P   iff   Bound B Q.
```

The result is *stronger* than the previously source-accepted conditional
`Bound 28311 P ↔ Bound 28311 Q`: it preserves the entire spectrum of possible
upper bounds, not just the conjectured sharp one.

## Proof

1. Any machine completing `Q` also completes `P`. Hence
   `Bound B P → Bound B Q` by the source refinement/compatibility lemma,
   for every `B`.
2. The exact accepted late 1LE halter has weighted score **28,311**.
   Therefore `Bound B Q` forces `B ≥ 28311`: if `B ≤ 28310`,
   monotonicity would contradict the certified 1LE unbounded-at-28310 theorem.
3. Every competing normalized A1 first-hole child has a certified weighted
   bound at most **15,125**, including the 0LE child. The nine-child accepted
   join `Raw39AcceptedNine.parent_bound_two` absorbs all other normalized
   A1 transitions, the fresh-state case and literal cycle/symmetry cases.
   Thus, when `B ≥ 28311`, `Bound B Q` and the monotone 0LE bound
   suffice to give `Bound B P`.
4. Combining both implications yields the theorem for all `B`.

The source proof is [Raw39ThresholdReduction.lean](Raw39ThresholdReduction.lean):
`oneLE_lower_bound` formalizes step 2 and `bound_iff_oneLE` formalizes
steps 1–4. The base ten-child join was independently source-accepted in
[run 46111414686](https://github.com/FlareZ123/bb6/actions/runs/46111414686),
artifact 15248719734; its transitive axioms were exactly `propext`,
`Classical.choice`, `Quot.sound`. The extra **all-threshold source audit**
is [CI 46111928725](https://github.com/FlareZ123/bb6/actions/runs/46111928725).
**Until that audit succeeds, do not report the new all-threshold statement as
an independently accepted Lean theorem.**

## Global consequence: a strictly weaker missing hypothesis

The accepted source-certified Canonical40 theorem contains `P` exactly
once (membership accepted [CI 46102358966](https://github.com/FlareZ123/bb6/actions/runs/46102358966)).
Removing `P` from the roster leaves 39 representatives, *provided that*
`Cover (WeightedBound 6766859) P` is supplied. By the theorem above, a
**single** condition `Bound 6766859 Q` suffices for that Cover; it is
strictly weaker than the specific sharp target `Bound 28311 Q`.

The proposed [Raw39SoleObligation.lean](Raw39SoleObligation.lean) encodes
both implications. It does not assert that `Bound 6766859 Q` has been proved:
that is exactly the outstanding 1LE *whole-child* decision. Nor does a
39-representative conditional quotient theorem prove BB(6), because its
other 39 Covers remain hypotheses. Direct source integration is handled by
[consume_raw39_after_canonical40.py](consume_raw39_after_canonical40.py)
and [CI 46111743603](https://github.com/FlareZ123/bb6/actions/runs/46111743603)
for the first version; the globally weaker version requires its own
source check after the all-threshold gate.

This reduction is directly reusable as a proof strategy for other partial
machines with one dominant child: obtain a concrete lower witness in the
dominant child strictly exceeding a uniform upper bound on every sibling,
and apply the accepted exhaustive child partition.
