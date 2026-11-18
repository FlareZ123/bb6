# Source-only closure on the U5 residual cylinder w = 1125 (mod 4096)

**Status: exact arithmetic derivation and Lean draft; not yet compiled or source-certified.** This is an intermediate result under im-results/, not an entry for results/.

## 1. Lift from w to the q-fan parameter

The U5 residual equations imply

```
211*t + 1360 + 22155*w = 20*2^(201+3360*w).
```

For w = 1125 (mod 4096), the right side is divisible by 4096 and

```
211*3875 + 1360 + 22155*1125 = 4096*6285
211*1883 = 4096*97 + 1.
```

Thus t = 3875 (mod 4096). Write t = 3875 + 4096*v. The same identity also gives t = 123 (mod 168) and the older z=193 (mod 512) parameterization, but the generalized q-fan proof needs only t = 3875 (mod 4096).

## 2. The exact q-fan has only q = 0, 1, or 2

For X_t=(44*t-1,42*t-1), the exact source-parent fan gives

```
43*t - 1 = 4^q * U,   U even,   a=U-2,
2*k + U + 6*q = 128*t - 8.
```

With t = 3875 + 4096*v,

```
43*t - 1 = 166624 + 176128*v = 96 (mod 128).
```

If q >= 3, then 128 divides 4^q*U because 64 divides 4^q and U is even. This contradicts the displayed residue. Hence q is one of 0, 1, or 2.

## 3. q=0 source-parent chain

The q=0 parent is

```
P0 = (166622+176128*v, 164684+174080*v).
```

It is even/even with sum 2 mod 4, so the complete source-parent fan forces its direct parent

```
D0 = (331304+350208*v, 82341+87040*v).
```

D0 has odd right coordinate and sum 1 mod 4, an established blank-image exclusion. Thus q=0 is impossible.

## 4. q=1 source-parent chain

The q=1 parent is

```
P1 = (41654+44032*v, 227165+240128*v).
```

It is even/odd with sum-plus-one 4 mod 8. The exact even/odd-four inverse gives

```
Q1 = (134407+142080*v, 180785+191104*v).
```

Q1 is odd/odd with sum 8 mod 16, so odd/odd valuation three gives

```
R1 = (157594+166592*v, 169188+178848*v).
```

R1 is even/even with sum 2 mod 4. Its forced direct parent is

```
D1 = (326780+345440*v, 84593+89424*v).
```

D1 has odd right coordinate and sum 1 mod 4, an established blank-image exclusion. Thus q=1 is impossible.

## 5. q=2 source-parent chain

The q=2 parent is

```
P2 = (10412+11008*v, 242783+256640*v).
```

It is even/odd with sum-plus-one 4 mod 8. The exact even/odd-four inverse gives

```
Q2 = (126595+133824*v, 184688+195232*v).
```

Q2 is odd/even with sum 3 mod 8, so the six-even-right theorem forces

```
R2 = (311281+329056*v, 92343+97616*v).
```

R2 is odd/odd with sum 8 mod 16. Odd/odd valuation three gives

```
S2 = (201810+213336*v, 147075+155476*v).
```

S2 has odd right coordinate and sum 1 mod 4, an established blank-image exclusion. Thus q=2 is impossible as well.

Together with q>=3 impossibility, all possible q branches terminate in established blank-image exclusions. This proves the source-only exclusion of X_t on the entire t = 3875 (mod 4096) cylinder, conditional only on the exact parent-fan and source-image lemmas in the Lean dependency closure.

## 6. End-to-end high-stop consequence

U5SourceOnlyHighStopW1021.lean lifts the generalized t = 3875 (mod 4096) q-fan exclusion through the exact U5 M8 six-even-right terminal chain and the original m=0 feeder. For every residual instance with w = 4096*n+1125, the q=0, q=1, and q=2 terminal parents are excluded above; q>=3 contradicts m+1 = 1 (mod 8); and the L_s feeder is excluded by the original mod-8 image invariant.

The existing residual nonemptiness theorem supplies s,m for every natural w, and s is strictly increasing with w for any two residual solutions. Therefore this gives an infinite nonempty sequence w=4096*n+1125 of authentic blank-unreachable high m=0 roots.

The root parameter remains j=39+64*s = 18791 (mod 32768), the same containing residue as the w=21, w=1021, and w=413 constructions. This is an additional residual-parameter cylinder, not a new root-index arithmetic-progression exclusion or a density increment. The older z=193 (mod 512) theorem remains as a corollary.

## 7. Files and verification boundary

- U5Q0SourceOnlyW1021.lean: generalized q=0/q=1/q=2 source exclusion for t = 3875 (mod 4096); the older z=193 (mod 512) theorem remains as a corollary.
- U5SourceOnlyHighStopW1021.lean: residual lift and end-to-end high-stop draft for w = 1125 (mod 4096).

No complete module in this directory has yet passed the required exact-source Lean 4.36.0-rc2 preflight and exported #print axioms audit. Do not describe this theorem as source-certified until the exact closure compiles and the axiom audit succeeds. Keep this material in im-results/; no results/ promotion is warranted yet.
