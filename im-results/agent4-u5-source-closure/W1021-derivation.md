# Source-only closure on the U5 residual cylinder w = 1021 (mod 1024)

**Status: exact arithmetic derivation and Lean draft; not yet compiled or source-certified.** This is an intermediate result under im-results/, not an entry for results/.

## 1. Lift from w to the q-fan parameter

The U5 residual equations are

```
211*s + 129 = 5*2^(201+3360*w)
32*s = 32 + 840*w + m
m+1 = 8*t+1.
```

Eliminating s and m gives the exact identity

```
211*t + 1360 + 22155*w = 20*2^(201+3360*w).
```

If w = 1021 (mod 1024), the right side is divisible by 1024. The exact arithmetic

```
211*459 + 1360 + 22155*1021 = 1024*22186
211*859 = 1024*177 + 1
```

therefore forces

```
t = 459 (mod 1024).
```

Write t = 459 + 1024*v. The same identity also yields t = 123 (mod 168), and hence the older parameterization t = 123 + 168*(128*v0+2). That additional CRT information is true but is no longer needed by the generalized q-fan exclusion below.

## 2. The exact q-fan has only q = 0 or q = 1

For an odd/odd target X_t = (44*t-1,42*t-1), the exact source-parent fan gives

```
43*t - 1 = 4^q * U,   U even,   a=U-2,
2*k + U + 6*q = 128*t - 8.
```

With t = 459 + 1024*v,

```
43*t - 1 = 19736 + 44032*v = 8 (mod 16).
```

Thus q >= 2 is impossible, because it would force 16 to divide 43*t-1. The only possible source parents are:

| branch | parent (a,k) | parity and sum |
|---|---|---|
| q=0 | (19734+44032*v, 19504+43520*v) | even/even, sum 2 mod 4 |
| q=1 | (4932+11008*v, 26902+60032*v) | even/even, sum 2 mod 4 |

## 3. q=0 source-parent chain

The complete even/even parent fan forces the direct parent at sum 2 mod 4. The exact even/odd-four and six-even-right source inverses then give

```
P0 = (19734+44032*v, 19504+43520*v)
  -> D0 = (39236+87552*v, 9751+21760*v)
  -> Q0 = (24491+54656*v, 17120+38208*v)
  -> R0 = (41609+92864*v, 8559+19104*v)
  -> S0 = (25082+55984*v, 16819+37544*v).
```

The exact gates are:

- P0 is even/even with sum 2 mod 4, so only its direct parent D0 remains.
- D0 is even/odd and D0.x + D0.y + 1 = 4 (mod 8), so its even/odd-four parent is unique and is Q0.
- Q0 has even right coordinate and Q0.x + Q0.y = 3 (mod 8), so the six-even-right theorem forces R0.
- R0 is odd/odd with sum 8 mod 16, so the odd/odd valuation-three parent is unique and is S0.
- S0 has odd right coordinate and sum 1 mod 4, an established blank-image exclusion.

Hence the q=0 parent cannot be blank-reachable.

## 4. q=1 source-parent chain

The q=1 parent also has even/even sum 2 mod 4. Two direct-parent reductions, followed by the sum-4-mod-8 direct-parent lemma and the even/odd-four inverse, give

```
P1 = (4932+11008*v, 26902+60032*v)
  -> D1 = (31832+71040*v, 13450+30016*v)
  -> D2 = (45280+101056*v, 6724+15008*v)
  -> D3 = (52002+116064*v, 3361+7504*v)
  -> Q3 = (27679+61784*v, 15519+34644*v).
```

Here D1 is even/even with sum 2 mod 4, so only its direct parent D2 remains. D2 is even/even with sum 4 mod 8. In the complete even/even source-parent fan, both the zero-left and even-a bounce alternatives have sums divisible by 8, so only the direct parent D3 can occur. D3 is even/odd with sum-plus-one 4 mod 8, hence its even/odd-four parent is uniquely Q3. Finally Q3 is odd/odd with sum 2 mod 4, another established blank-image exclusion.

Hence the q=1 parent cannot be blank-reachable either. Together with q>=2 impossibility, this proves the source-only exclusion of X_t on the entire t = 459 (mod 1024) cylinder, conditional only on the exact parent-fan and source-image lemmas in the Lean dependency closure.

## 5. End-to-end high-stop consequence

U5SourceOnlyHighStopW1021.lean lifts the generalized q=0 exclusion through the existing exact U5 M8 six-even-right terminal chain and the original m=0 feeder:

```
high m=0 root -> A_s -> L_s or B_s
L_s: excluded by the mod-8 image invariant
B_s: exact six-even-right chain -> terminal y=3
terminal y=3: q=0 excluded above; q=1 odd-right sum two; q>=2 contradicts m+1=1 (mod 8).
```

The exact residual identity and w = 1021 (mod 1024) give t = 459 (mod 1024), which is precisely the generalized q-fan hypothesis. The existing nonemptiness theorem supplies s,m for every natural w, so this gives an infinite nonempty sequence w = 1024*n+1021 of authentic blank-unreachable high m=0 roots.

The root parameter remains j=39+64*s = 18791 (mod 32768), the same containing residue as the earlier w=21 and w=37 constructions. This is an additional residual-parameter cylinder, **not** a new root-index arithmetic-progression exclusion or a density increment. The root indices grow exponentially along the sequence.

## 6. Files and verification boundary

- U5Q0SourceOnlyW1021.lean: exact q=0/q=1 parent-chain draft for t = 459 (mod 1024), plus the older z=2 (mod 128) statement as a corollary.
- U5SourceOnlyHighStopW1021.lean: residual lift and end-to-end high-stop draft.
- U5Q0SourceOnly.lean and U5SourceOnlyHighStop.lean: the earlier t=19 (mod 32), t=99 (mod 128), and w=21 (mod 32) source-only drafts.

No complete module in this directory has yet passed the required exact-source Lean 4.36.0-rc2 preflight and exported #print axioms audit. A previous invocation compiled only isolated arithmetic fragments; this invocation's local shell and Python tools returned a tool-level ClientError. No CI was dispatched. Agent 24 has been asked to compile the exact complete transitive source closure, including the current generalized W1021 modules, if its local runtime is available.

Do not describe these new theorems as source-certified until the exact closure compiles and the axiom audit succeeds. Keep this material in im-results/; no results/ promotion is warranted yet.
