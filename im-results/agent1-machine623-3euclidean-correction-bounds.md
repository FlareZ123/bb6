# Uniform magnitude bounds for the exact #623 3-Euclidean corrections

**Status:** exact derivation from the source-level `evalA`/`drainB` lemmas already present in the repository; not yet packaged as a Lean theorem. This is a correction-size result, not a proof of the all-time root-gap bound.

## Setup

Use the four canonical ray bases from `TernaryShiftSource.lean` and the correction coordinates from `ExactRayCorrectionRelations.lean`:

```
beta  = B - c - v,
delta = E - 3m,
```

where the corresponding base drain returns `D(B,E)`. The exact weighted identities already formalized there are

```
left odd/even:  2 beta + delta = 2r + 4,
right odd:      2 beta + delta = 2r + 8,
right even:     2 beta + delta = 2r + 7,
```

with `r` the outer `drainB` iteration count.

The source-level bounds used below are:

- `drainB_first_upper_log`: if the drain budget `b < 3^n`, then its output first counter `B <= a+n`;
- `drainB_weighted_depth`: under the same hypothesis, `r <= n`;
- `evalA_first_upper_one`: an `evalA` call raises its first counter by at most one;
- `evalA_ones_budget`: an `evalA` output `(a1,b1,d1)` satisfies `b1 <= ternaryOnes a1`;
- `evalA_weighted_exact` and `drainB_weighted_exact`: the exact weighted identities.

Also use `ternaryOnes n = (3^n-1)/2 < 3^n).

## Four sector bounds

All bounds below are uniform in the other canonical coordinate.

### Left odd

The canonical exponent `k` satisfies `d+3 <= ternaryOnes k`, and the base drain is

```
drainB k (d+3) 5 = some (D B E).
```

Thus `d+3 < 3^k`, so `B <= k+k = 2k` and `r <= k`. The weighted identity gives

```
2B+E = 2k + 5 + 3(d+3) + 2r
     = 3d + 2k + 14 + 2r.
```

With `beta=B-5-k`, `delta=E-3d`:

```
-(k+5) <= beta <= k-5,
14-2k <= delta <= 4k+14,
|beta| <= k+5,       |delta| <= 4k+14.
```

### Left even

The canonical exponent satisfies `d+2 <= ternaryOnes k`, and

```
drainB k (d+2) 2 = some (D B E).
```

Again `B<=2k`, `r<=k`. The weighted identity is

```
2B+E = 2k + 2 + 3(d+2) + 2r
     = 3d + 2k + 8 + 2r.
```

With `beta=B-2-k`, `delta=E-3d):

```
-(k+2) <= beta <= k-2,
8-2k <= delta <= 4k+8,
|beta| <= k+2,       |delta| <= 4k+8.
```

### Right odd

The canonical exponent satisfies `a-1 <= ternaryOnes (2k+5)`, and

```
drainB (2k+5) (a-1) 3 = some (D B E).
```

Hence `a-1 < 3^(2k+5)`, so `B<=4k+10` and `r<=2k+5`. The weighted identity is

```
2B+E = 2(2k+5) + 3 + 3(a-1) + 2r
     = 3a + 4k + 10 + 2r.
```

With `beta=B-1-2k`, `delta=E-3a`:

```
-(2k+1) <= beta <= 2k+9,
-4k-10 <= delta <= 8k+20,
|beta| <= 2k+9,     |delta| <= 8k+20.
```

### Right even

The canonical exponent satisfies `a < ternaryOnes (2k+3)`. The initial evaluator is

```
evalA (2k+3) a (2a+5) = some (a1,b1,d1).
```

By `evalA_first_upper_one`, `a1<=2k+4`. By `evalA_ones_budget`, `b1<=ternaryOnes a1<3^a1`, so the subsequent drain has `r<=a1<=2k+4` and `B<=a1+a1<=4k+8`.

Combining the two weighted identities gives

```
2B+E = 2a1+3b1+d1+2r
     = 2(2k+3) + a + (2a+5) + 2r
     = 3a + 4k + 11 + 2r.
```

With `beta=B-2-2k`, `delta=E-3a`:

```
-(2k+2) <= beta <= 2k+6,
-4k-5 <= delta <= 8k+19,
|beta| <= 2k+6,     |delta| <= 8k+19.
```

## Consequence for the 3-Euclidean coordinates

Let `p=|a-d|`, `q=min(a,d)`, `g=p-3q`. The exact updates in the two orientations are

```
left:  p' = g + beta - delta,  q' = 3q + delta,
right: p' = -g + delta - beta, q' = p + beta.
```

Consequently the deviation from the ideal 3-Euclidean map is logarithmic in the canonical exponent:

| sector | `|p' - p'_ideal|` | `|q' - q'_ideal|` | `|g' - g'_ideal|` |
|---|---:|---:|---:|
| left odd | `<= 5k+19` | `<= 4k+14` | `<= 17k+61` |
| left even | `<= 5k+10` | `<= 4k+8` | `<= 17k+34` |
| right odd | `<= 10k+29` | `<= 2k+9` | `<= 16k+56` |
| right even | `<= 10k+25` | `<= 2k+6` | `<= 16k+43` |

Here the ideal gap updates are `g-9q` on the left and `-4g-9q` on the right. For the right-even sector, `k` is half the canonical exponent parameter, so the displayed bounds are still logarithmic in the scale.

This makes the exact ray a genuinely `O(log scale)` perturbation of the ideal 3-Euclidean dynamics, with explicit sector constants. It does **not** by itself prove a root-gap lower bound: the cancellation windows `g≈9q` and `4g≈-9q` still require an arithmetic or dynamical exclusion. It does, however, give a quantitative error budget against which a square-distance invariant can be tested.

## Existing source dependencies

- `im-results/agent22-623-root-ray-20k/ExactDrainCocycleSource.lean`
- `im-results/agent22-623-root-ray-20k/ExactDrainCocycleDepthSource.lean`
- `im-results/agent22-623-root-ray-20k/DrainLinearLogSource.lean`
- `im-results/agent22-623-root-ray-20k/ExactRayCorrectionRelations.lean`
- `im-results/agent49-parity623/TernaryBufferSource.lean`
- `im-results/agent49-parity623/TernaryShiftSource.lean`


## Direct reduction to the source-proved terminal corridor

Agent49's source theorem `next_none_requires_k_gap` says that if
`2(a'+d')+5 < 3^K`, then any terminal accelerated state `D(a',d')` must satisfy

```
|a'-d'| < K+5.
```

Thus a genuine terminal state is confined to a logarithmic diagonal corridor.

For one exact 3-Euclidean transition, the actual next difference is
`p' = |g + beta - delta|` on the left and
`p' = |-g + delta - beta|` on the right, where `g=p-3q`.
The reverse triangle inequality gives

```
left odd:  |p' - |g|| <= 5k+19
left even: |p' - |g|| <= 5k+10
right odd: |p' - |g|| <= 10k+29
right even:|p' - |g|| <= 10k+25.
```

Consequently, a root-sensitive lower bound
`|g| > K+5 + E_sector(k)`, with `E_sector` the corresponding displayed error, rules out a terminal successor.

A fixed positive square-gap estimate `g^2 >= C*q` is sufficient asymptotically, with a simple scale split. If `|g|<=q`, then `p=3q+g<=4q`, so the current and next coordinate scales are O(q) (the exact scale correction is O(k)); hence `K=O(log q)`, while `|g|>=sqrt(Cq)`. If `|g|>q`, then the output difference is `|g|+O(k)), and the output coordinate scale is O(q+|g|)=O(|g|); thus `K=O(log |g|)`, which is dominated by `|g|`. In both cases the O(k) correction and terminal corridor are eventually smaller than the gap. The remaining finite prefix can be checked exactly.

This is a sufficient reduction, not an established root invariant: the all-time square-gap estimate for the actual D(0,7) orbit remains unproved.
