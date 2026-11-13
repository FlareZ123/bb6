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
