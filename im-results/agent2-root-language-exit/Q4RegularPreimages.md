# Exact regular-model preimages of the q=4 root cylinder

This note is an arithmetic constraint for the open blank-root connection in
`im-results/agent37-echain/EERootBEA.lean`. It is **not** a physical blank-root
reachability theorem.

## Target

The source-certified E/E/B/E/reset/BEA closure applies to

```
L(59049*m + 44494, 4, 1)
= L(9*t + 7, 4, 1),  t = 6561*m + 4943,  t ≡ 2 (mod 27).
```

Equivalently write the larger q=4 cylinder as
`L(243*u+25,4,1)`, where the EERootBEA subfamily has
`u=243*m+183`.

## Exhaustive one-step preimage calculation

Use the explicit eleven-case arithmetic table in
`DRegularFirstExit.step`:

- If the predecessor has `a=3k+2), then a q-positive B step maps
  `(3k+2,q,b)` to `(8k+10,q-1,b)`.
- If the predecessor has `a=3k+4` and `b≥3), then the E step maps
  `(3k+4,q,b)` to `(8k+9,q+2,b-3)`.

No other branch can output q=4,b=1. Therefore every one-step regular
predecessor of `(a,4,1)` is exactly one of:

```
(3k+2, 5, 1),  a = 8k+10;
(3k+4, 2, 4),  a = 8k+9.
```

For `a=243*u+25`, the first equation requires
`3*u+1 ≡ 2 (mod 8)`, i.e. `u ≡ 3 (mod 8)`; the second requires
`3*u+1 ≡ 1 (mod 8)`, i.e. `u ≡ 0 (mod 8)`.

For the narrower EERootBEA parameterization `u=243*m+183`, these become:

| Target parameter | Required predecessor |
|---|---|
| `m=8*j+4` | `(177147*j+105257, 5, 1)` |
| `m=8*j+3` | `(177147*j+83116, 2, 4)` |

The formula follows by substituting the two residue classes into
`k=(a-10)/8` or `k=(a-9)/8` respectively.

## How to use this

Once a root-chain computation identifies an actual q=4 exceptional section,
check its full residue `a mod 59049` against 44494. If it matches, the
source theorem `q4_exceptional_EE_BEA_section` supplies the subsequent
physical regular return. The predecessor formula is a useful consistency
check and narrows the final edge of the regular model, but the root prefix
must still be proved from the original blank configuration with
`DRegularSource` / `ObsEq`; model reachability alone is insufficient.


## Exact initial state after the thirtieth reentry

From `BlankThirtiethRejoin.lean`:

- `packet30.a=24*t30+21`, so `k30=8*t30+6`;
- `packet30.p=16), so `r30=5`;
- `wordInc(aWords 0 5)=29), hence `aUnary k30 0 5 = 8*k30+69).

Therefore the pure-unary seed31 is exactly

```
seed31 = L(64*t30+117, 0, 0),    t30 ≡ 22 (mod 27).
```

The first three DRegular transitions are consequently fixed by the known
mod-27 residue:

```
L(64*t+117, 0, 0)
  -> L((512*t+919)/3, 1, 5)
  -> L((4096*t+7439)/9, 0, 0)
  -> L((32768*t+59593)/27, 0, 0).
```

The divisibilities and branch conditions follow from `t≡22 (mod27)`.
The fourth transition depends on `t mod81), which is not supplied by
`terminal2613_certificate`; do not extrapolate the trajectory from the
mod-27 fact alone. The `Seed31Probe` is intended to compute the exact
first exit from the full integer seed.


## Comparison with the distinct sixth-root q=4 subfamily

The already source-composed `BlankSixthQ4Rejoin.q4_mod9_rejoin` covers
`sourceStart (9*s+7) 4`, whose DRegular state is
`L(243*s+214,4,1)` (equivalently `t≡23 (mod27)`). This is distinct from
the EERootBEA target `a≡25 (mod243)`.

The same one-step table gives the following immediate predecessors of this
second q=4 subcylinder:

- If `s≡4 (mod8)`, write `s=8*j+4`; predecessor is
  `(729*j+443,5,1)`.
- If `s≡1 (mod8)`, write `s=8*j+1`; predecessor is
  `(729*j+172,2,4)`.

These are model-level predecessor conditions only. They do not imply that
the blank orbit reaches either q=4 subfamily.


Putting `t30=27*r+22` makes the same three-step segment especially
transparent:

```
seed31 = L(1728*r+1525, 0, 0)
  -> L(4608*r+4061, 1, 5)
  -> L(12288*r+10839, 0, 0)
  -> L(32768*r+28907, 0, 0).
```

The fourth branch is determined by `r mod 3`, since the last displayed
unary parameter is congruent to `2*(r+1) (mod 3)`: residues
`r=0,1,2 (mod 3)` select respectively the `a≡2,1,0 (mod 3)` branches.
The known `t30 mod27` does not determine `r mod3`; equivalently, the
existing certificate does not determine `t30 mod81`.
