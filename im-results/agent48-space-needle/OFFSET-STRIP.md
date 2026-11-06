# Space Needle: universal fourth-linear terminal valuation cutoff

**Status (6 November 2026):** New all-natural theorem locally compiled with Lean 4.36.0-rc2, `#print axioms` exactly `[propext, Quot.sound]` and no sorry or custom axioms. The original-machine bridge is locally typechecked against exact source-signature stubs but has **not yet passed pinned Cryptids CI**. No blank-root halting result is asserted.

## Sharp new necessary inequality

Let `q,v,K` be arbitrary natural numbers satisfying the exact Space Needle terminal source equation

```
2^K = (2^(v+1)+3)*q + (3*2^v+v+3).
```

Combining [Agent20's original-source sharp bound](../agent20-needle-coprime/NeedleSharper.lean) with the new [Lean-certified strip obstruction](OffsetStrip.lean) gives

```
(q,v,K)=(61,6,13)  OR  4*v ≤ K+2.
```

The exception is the *same unique synthetic* predecessor previously isolated by Agent 20. The general restriction `4v≤K+2` is strictly stronger than the previous `3v+3≤K` for `v≥6`, and it reduces the maximum tested valuation in a complete terminal inverse enumeration from approximately `K/3` to `K/4` (plus the explicit exception). It does not imply a blank-reachable source exists.

## All-offset theorem behind the improvement

For every natural `q,v,s`, the theorem `no_narrow_terminal_strip` proves

```
2^(3v+3+s) = (2^(v+1)+3)*q + (3*2^v+v+3)
    ⇒ v ≤ s+5.
```

This is an explicit **uniform linear exclusion of all narrow strips** above the earlier `3v+3` wall. To derive the new inequality, put `s=K-(3v+3)`; then `v≤s+5` rearranges to `4v≤K+2`.

### Proof mechanism

Write `x=2^(v+1)` and `y=2^s`. The equation implies

```
2*y*x^3+54*y+3 = (x+3)*(2*q+3)+(2v+54*y).
```

Combine with the exact polynomial identity

```
(x+3)*(2*y*x^2+18*y)
  = 2*y*x^3+54*y+6*y*x*(x+3).
```

A positive-integer factorization then forces

```
2^(v+1)+3 divides 2v+54*2^s-3.
```

If `v≥s+6`, the elementary inequalities `2v≤2^v` and `54*2^s≤2^v` give

```
0 < 2v+54*2^s-3 < 2^(v+1)+3,
```

contradicting the divisibility. Every step is a symbolic all-natural Lean proof. The argument is independent of any simulation horizon or finite maximum for `K` or `v`.

## Verification and research use

- [OffsetStrip.lean](OffsetStrip.lean): locally kernel-verified `no_narrow_terminal_strip` and `stronger_from_sharp`. Only foundational `propext` and `Quot.sound` axioms. All-natural quantification.
- [OffsetStripSource.lean](OffsetStripSource.lean): direct original-`highLevelNext` bridge to `NeedleSharper.sharper_valuation_bound`. The stub used for local typing replaces *only* imported source declarations; authentic upstream source audit is pending. [Manual workflow](../../.github/workflows/agent48-space-needle-five.yml) includes the complete dependency compilation against unchanged pinned source.
- [BoundaryExact.lean](BoundaryExact.lean) separately classifies exact equality `K=3v+3` as the two known triples `(45,2,9)`, `(214,3,12)` via an exact iff.
- Practical next task: adapt the source-certified complete terminal inverse list [NeedleCubicEnumerate.lean](../agent20-needle-coprime/NeedleCubicEnumerate.lean) to the new `⌊(K+2)/4⌋` ceiling with exceptional entry. This may accelerate genuine fixed-target blank-root backward search.
- Original machine's blank orbit starting at `N 1` is unaffected as a logical conclusion. **BB(6) remains unsolved.** External novelty and peer-review status are unknown.
