# Exact-mass and exact-length synthetic power-gate completions for S4

**Scope:** Elementary mathematical construction for the first `G 509` gate of the S4 reduced return map. This is a structural limitation on coarse root invariants. It does not prove that the authentic root halts or survives.

## Theorem

Let `L >= 3`, `k >= 0`, and `m >= (L-3) + max(10, k + 2^L)`.
There is a finite natural-number digit stack `S` satisfying **all three** conditions

1. `S.length = L`;
2. `sum (S.map (·+1)) = m`;
3. `W(S) + k = 2^e` for some nonnegative integer `e`,

where `W([])=0` and `W(b::T)=b+1+2*W(T)`.

Consequently, if `u` is an S4 digit prefix of exactly nine entries and
`W(u)+509=512*k`, then `G 509 (u++S)=none` by the original-source
`G_none_iff_power` theorem, while the suffix `S` has any prescribed
length `L` and mass `m` satisfying the bound.

## Constructive proof

Write `t=m-(L-3)` and `K=k+2^L-8`. The hypothesis gives
`t >= 10` and `t >= K+8`. Take the least power of two
`p=2^e >= t+K+4`. The elementary dyadic-bracket lemma gives
`p < 2*(t+K+4)`. Put `w=p-K`. These inequalities imply

```
t+4 <= w < 2*t+K+8 <= 3*t.
```

Set `d=w-t`, `q=(d-1)//3` and `r=d-3*q`.
Thus `q>=1`, `1<=r<=3`, and `a0=t-r-q>=1`; the last
inequality follows from `t>=10` and `d<2*t`.
Take

```
S = [a0-1, r-1, q-1] ++ [0] * (L-3).
```

Its first three positive unary-block masses are `a0,r,q` and sum to
`t`. Its last `L-3` block masses are one each, so its total mass
is `t+(L-3)=m` and length is `L`. Its weighted value is

```
W(S) = a0 + 2*r + 4*q + sum(2^i for i=3..L-1)
     = t+r+3*q+2^L-8
     = w+2^L-8.
```

Therefore `W(S)+k=w+K=p=2^e`. The standard concatenation identity

```
W(u++S) = W(u) + 2^len(u)*W(S)
```

gives `W(u++S)+509=512*(k+W(S))=2^(e+9)` at length nine.
This proves the S4 gate stopping criterion for the synthetic suffix.

## Relation to Lean and the real root

- `S4MassCompletion.lean` and `S4MassDyadicPower.lean` prove in Lean 4.36.0-rc2 the universal weighted-mass representation and dyadic-bracket theorems with arbitrary **at-most-three-digit** suffixes.
- `S4MassBridge.lean` proves the corresponding nine-digit first-gate completion and weighted concatenation law in Lean.
- `S4MassSourceGate.lean` imports the original S4 `G_none_iff_power` theorem and concludes exact-mass synthetic `G 509` failure. Original-source CI was pending when this note was written.
- The stronger **exact-length** construction above is a direct mathematical argument, additionally supported by the deterministic `ninth_same_shape_witness.py` checker.

The verified original S4 reduced root reaches return 5457 with 18 digits.
The source-shaped finite interpreter checked each of its next 81,920
returns and encountered 118 first-gate residue phases. At all 118,
the authentic simulated suffix had length 9 or 13 and enough mass for
the theorem above. The checker generated a synthetic suffix matching
the **first nine digits, full-stack length, and full-stack mass** of
the authentic state, then verified the synthetic `G 509` halts and
the genuine simulated `G 509` succeeds. The length distribution is
38 occurrences of length 9 and 80 of length 13; the smallest original
suffix-mass-minus-`k` margin is 5,770,295.

The final paragraph is finite numerical evidence beyond the Lean-certified
return 5457. It is not an all-time rooted theorem. Equal prefix, length,
and mass do not imply equal reachability, and this is precisely the
information gap the genuine BB(6) solution must address.
