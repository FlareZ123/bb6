# Agent 40: two constructive Sheep even-section chain certificates

**Scope:** exact all-index source-shaped generic predecessor *existence* for the two
chain-type power families in Agent14's [four-cone note](../agent14-sheep-even-inverse/ROOT-FREE-CONES.md):
`j=402+4860k` and `j=1738+4860k`, for every natural `k`.
This is verification and source-transport progress on previously identified
families, not a new excluded class, a complete predecessor-classification
proof, a Sheep classification, or a BB(6) solution.

## Checked mathematics

In [ChainWitnesses.lean](ChainWitnesses.lean), the exact
`SheepEvenInverseAlgebra.GenericEdge` formula is copied as the *definitionally
identical* independent predicate `Audit.GenericEdge`. The following
two fully quantified theorems compile locally in **Lean 4.36.0-rc2** with
only `[propext, Quot.sound]` (and no `sorryAx`):

- `Audit.chain402 (k)`: there are even `B<A<R=2^(402+4860k)`,
  all greater than 10, with genuine generic arithmetic edges
  `B → A → R`. Exactly `15A+2=8R` and `1485B+4688=512R`.
- `Audit.chain1738 (k)`: analogous `B → A → R=2^(1738+4860k)`,
  with `15A+2=8R` and `135B+196=64R`.

The proof has only two modular gates, each proved **uniformly in k** using
exact modular period reduction:

```
2^(402+4860k) % 2970 = 334
2^(1738+4860k) % 270 = 214
```

The constructive witnesses do not require huge numerals. Set `q=R/2970`
in the 402 case, so `R=2970q+334`. Then

```
A = 2*(792q+89)
B = 16*(64q+7)
root odd block u = 990q+111
child odd block u = 528q+59
generic edge parameters: (a,h)=(1,1), then (4,1)
```

For 1738 set `q=R/270`, so `R=270q+214`:

```
A = 2*(72q+57)
B = 4*(32q+25)
root odd block u = 90q+71
child odd block u = 144q+113
generic edge parameters: (a,h)=(1,1), then (2,0)
```

All valuations, oddness, lower bounds, identities, and strict edge
inequalities are checked for arbitrary `k` in Lean, with no finite-index
extrapolation. Periods of 2 modulo the **odd** moduli 1485 and 135 are
180 and 36, both dividing 4860. The factor 2 in the displayed stronger
moduli is handled by explicit evenness. In particular, it would be incorrect
to assert `2^180 % 2970=1`; the proof avoids that common period error.

## Original-source bridge

[ChainSourceWitnesses.lean](ChainSourceWitnesses.lean) imports Agent40's
already source-checked `SheepGenericConverse.generic_to_source` and obtains
original `SheepEven.EvenEdge` witnesses for **both** arrows of both families,
keeping all integer identities. The source wrapper must be checked with the
authentic original-source dependency stack. Until a CI source build actually
finishes successfully, report the above as local kernel-certified
**algebra** and the wrapper as a pending source-import validation.

## Remaining obstruction

Existence of both displayed chain edges does not imply **absence of other
predecessors** of `R`, `A` or `B`. The full exact three-state basin claim
in Agent14's note separately invokes all-high-h, all-high-a, exceptional
branch, and full-period low valuation exclusions. This contribution improves
one part of the authentic-branch sufficiency proof and supplies concise
reusable all-k Lean witnesses. A complete genuine-blank exclusion for these
two power families still requires integrating and verifying those
**no-additional-parent** certificates.

External publication novelty has not been evaluated. The exact BB(6)
function remains unknown.
