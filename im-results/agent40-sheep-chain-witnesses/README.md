# Agent 40: two constructive Sheep even-section chain certificates

**Scope:** exact all-index source-shaped generic predecessor *existence* for three
families (two chains and one fork) in Agent14's [four-cone note](../agent14-sheep-even-inverse/ROOT-FREE-CONES.md):
`j=402+4860k` and `j=1738+4860k`, for every natural `k`.
This is verification and source-transport progress on previously identified
families, not a new excluded class, a complete predecessor-classification
proof, a Sheep classification, or a BB(6) solution.

## Checked mathematics

In [ChainWitnesses.lean](ChainWitnesses.lean) and [Fork1218.lean](Fork1218.lean), the exact
`SheepEvenInverseAlgebra.GenericEdge` formula is copied as the *definitionally
identical* independent predicate `Audit.GenericEdge`. The following
three fully quantified theorems compile locally in **Lean 4.36.0-rc2** with
only `[propext, Quot.sound]` (and no `sorryAx`):

- `Audit.chain402 (k)`: there are even `B<A<R=2^(402+4860k)`,
  all greater than 10, with genuine generic arithmetic edges
  `B → A → R`. Exactly `15A+2=8R` and `1485B+4688=512R`.
- `Audit.chain1738 (k)`: analogous `B → A → R=2^(1738+4860k)`,
  with `15A+2=8R` and `135B+196=64R`.

- `Audit.fork1218 (k)`: two distinct genuine generic arrows `A → R ← B`,
  where `R=2^(1218+4860k)`, `15A+2=8R`, and `81B+68=32R`.
  Both source states are strictly between 10 and the root power.

The three proofs each reduce to a single modular gate, each proved **uniformly in k** using
exact modular period reduction:

```
2^(402+4860k) % 2970 = 334
2^(1738+4860k) % 270 = 214
2^(1218+4860k) % 810 = 154
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

For 1218 set `q=R/810`, `R=810q+154`, `A=2(216q+41)`,
`B=4(80q+15)`, and odd blocks `270q+51` and `90q+17`.
The associated generic parameters are `(a,h)=(1,1)` and `(2,2)`.

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

[ChainSourceWitnesses.lean](ChainSourceWitnesses.lean) and
[Fork1218Source.lean](Fork1218Source.lean) import Agent40's
already source-checked `SheepGenericConverse.generic_to_source` and obtains
original `SheepEven.EvenEdge` witnesses for **all** displayed arrows of all three families,
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
three power families still requires integrating and verifying those
**no-additional-parent** certificates.

External publication novelty has not been evaluated. The exact BB(6)
function remains unknown.

## New finite-root modular completeness component

A new reusable Lean module [SheepPeriodicGate.lean](SheepPeriodicGate.lean) proves that a complete finite modular cycle for `2^(base+4860*k)` rules out the corresponding generic predecessor equation for every natural `k` and **every natural odd-block coefficient `v`**, without requiring parity of `v`. Source: [generate_low.py](generate_low.py) generates 106 separate all-index Lean theorems for every unwanted small `(h,a)` generic candidate among the three nodes each of the 402 and 1738 chains. The four surviving cells are precisely `(402,node0,h1,a1)`, `(402,node1,h1,a4)`, `(1738,node0,h1,a1)`, and `(1738,node1,h0,a2)`, matching the constructive arrows above. It checks 106 complete cycles (maximum 17 `k`-classes) and independent precise odd-modulus periodicity before emitting each Lean theorem. All 106 theorems compiled locally under Lean 4.36.0-rc2, using `Nat.powMod_def` to make the finite modular witnesses kernel-efficient. Sample axiom audits returned `[propext, Quot.sound]`; no `sorryAx`. Exact low-valuation proof is now kernel-backed, pending genuine-source integration and high-valuation/exceptional completeness.

**Pinned original-source verification of positive edges:** manual workflow [41934888623](https://github.com/FlareZ123/bb6/actions/runs/41934888623) SUCCESS for the two chains, and expanded run [41935472169](https://github.com/FlareZ123/bb6/actions/runs/41935472169) SUCCESS for the r1218 fork. The source checks were executed on upstream Cryptids and Lean 4.35.0-rc4, distinct from the local modular-gate compilation.
