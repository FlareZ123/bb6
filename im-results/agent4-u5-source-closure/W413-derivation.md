# Source-only closure on the U5 residual cylinder w = 413 (mod 1024)

**Status: exact arithmetic derivation and Lean draft; not yet compiled or source-certified.** This is an intermediate result under im-results/, not an entry for results/.

## 1. Lift from w to the q-fan parameter

The U5 residual equations imply

```
211*t + 1360 + 22155*w = 20*2^(201+3360*w).
```

For w = 413 (mod 1024), the right side is divisible by 1024 and

```
211*811 + 1360 + 22155*413 = 1024*9104
211*859 = 1024*177 + 1.
```

Thus t = 811 (mod 1024). Write t = 811 + 1024*v. The same residual identity also gives t = 123 (mod 168), hence the older z=126 (mod 128) parameterization, but the generalized q-fan proof needs only t = 811 (mod 1024).

## 2. The exact q-fan has only q = 0 or q = 1

For X_t=(44*t-1,42*t-1), the exact source-parent fan gives

```
43*t - 1 = 4^q * U,   U even,   a=U-2,
2*k + U + 6*q = 128*t - 8.
```

With t = 811 + 1024*v,

```
43*t - 1 = 34872 + 44032*v = 8 (mod 16).
```

Therefore q >= 2 is impossible. The only possible source parents are:

| branch | parent (a,k) | parity and sum |
|---|---|---|
| q=0 | (34870+44032*v, 34464+43520*v) | even/even, sum 2 mod 4 |
| q=1 | (8716+11008*v, 47538+60032*v) | even/even, sum 2 mod 4 |

## 3. q=0 source-parent chain

The q=0 parent is forced through one direct even/even parent, one even/odd-four parent, and four six-even-right parents:

```
P0 = (34870+44032*v, 34464+43520*v)
  -> D0 = (69332+87552*v, 17231+21760*v)
  -> Q0 = (43279+54656*v, 30254+38208*v)
  -> R0 = (73531+92864*v, 15126+19104*v)
  -> S0 = (88655+111968*v, 7562+9552*v)
  -> T0 = (96215+121520*v, 3780+4776*v)
  -> U0 = (99993+126296*v, 1889+2388*v).
```

The exact gates are:

- P0 is even/even with sum 2 mod 4, so only its direct parent D0 remains.
- D0 is even/odd and D0.x + D0.y + 1 = 4 (mod 8), so its even/odd-four parent is uniquely Q0.
- Q0, R0, S0, and T0 have even right coordinates and sums respectively 5, 1, 1, and 3 modulo 8. Each satisfies the six-even-right source gate, forcing the next displayed parent.
- U0 is odd/odd with sum 2 mod 4, an established blank-image exclusion.

Thus the q=0 parent cannot be blank-reachable.

## 4. q=1 source-parent chain

The q=1 parent is even/even with sum 2 mod 4. Its forced direct parent is

```
D1 = (56252+71040*v, 23768+30016*v).
```

D1 is even/even with sum 4 mod 8, so the complete even/even parent fan again forces its direct parent

```
D2 = (80018+101056*v, 11883+15008*v).
```

D2 has odd right coordinate and sum 1 mod 4, an established blank-image exclusion. Hence q=1 is impossible as well.

## 5. End-to-end high-stop consequence

U5SourceOnlyHighStopW1021.lean lifts the generalized t = 811 (mod 1024) q-fan exclusion through the exact U5 M8 six-even-right terminal chain and the original m=0 feeder. For every residual instance with w = 1024*n+413, the q=0 terminal parent is excluded by this theorem; the q=1 terminal parent is excluded by odd-right sum two; and q >= 2 contradicts m+1 = 1 (mod 8). The L_s feeder is excluded by the original mod-8 image invariant.

The existing residual nonemptiness theorem supplies s,m for every natural w, and s is strictly increasing with w for any two residual solutions. Therefore this gives an infinite nonempty sequence w=1024*n+413 of authentic blank-unreachable high m=0 roots.

The root parameter remains j=39+64*s = 18791 (mod 32768), the same containing residue as the w=21 and w=1021 constructions. This is an additional residual-parameter cylinder, not a new root-index arithmetic-progression exclusion or a density increment.

## 6. Files and verification boundary

- U5Q0SourceOnlyW1021.lean: generalized q=0/q=1 source exclusion for t = 811 (mod 1024); the older z=126 (mod 128) theorem remains as a corollary.
- U5SourceOnlyHighStopW1021.lean: residual lift and end-to-end high-stop draft for w = 413 (mod 1024).

No complete module in this directory has yet passed the required exact-source Lean 4.36.0-rc2 preflight and exported #print axioms audit. Do not describe this theorem as source-certified until the exact closure compiles and the axiom audit succeeds. Keep this material in im-results/; no results/ promotion is warranted yet.
