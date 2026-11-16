# Source-only closure on the U5 residual cylinder w = 1021 (mod 1024)

**Status: exact arithmetic derivation and Lean draft; not yet compiled or source-certified.** This is an intermediate result under `im-results/`, not an entry for `results/`.

## 1. Lift from w to the q-fan parameter

The U5 residual equations are

```
211*s + 129 = 5*2^(201+3360*w)
32*s = 32 + 840*w + m
m+1 = 8*t+1.
```

The exact pullback identity is

```
211*t + 1360 + 22155*w = 20*2^(201+3360*w).
```

Assume `w = 1021 + 1024*n`. Then the right side is divisible by 1024. Since

```
211*459 + 1360 + 22155*1021 = 1024*22186
211*859 = 1024*177 + 1,
```

the identity gives `t = 459 (mod 1024)`.

The same identity modulo 3, 7, and 8 gives:

- `t = 0 (mod 3)`, since the exponent is odd and `2^r = 2 (mod 3));
- `t = 4 (mod 7)`, since the exponent is divisible by 3 and `2^r = 1 (mod 7));
- `t = 3 (mod 8)`, since `t+w = 0 (mod 8)` and `w = 5 (mod 8)`.

Thus `t = 123 (mod 168)), so write `t=123+168*z`. Combining with `t=459 (mod 1024)` gives

```
168*z = 336 (mod 1024)
21*z = 42 (mod 128)
z = 2 (mod 128).
```

So the residual cylinder `w=1021 (mod 1024)` lands exactly in the q-fan cylinder

```
t = 123 + 168*(128*v+2).
```

## 2. The exact q-fan has only q = 0 or q = 1

For `t=123+168*z`, the q-fan equation is

```
43*t - 1 = 4^q * U,   U even,   a=U-2,
2*k + U + 6*q = 128*t - 8.
```

With `z=128*v+2`,

```
661 + 903*z = 2467 + 231168*v = 3 (mod 4),
43*t - 1 = 8*(661+903*z) = 8 (mod 16).
```

Therefore `q>=2` is impossible, because it would make `16` divide `43*t-1`.

The two remaining exact source parents are:

| branch | parent `(a,k)` | parity and sum |
|---|---|---|
| q=0 | `(19734+924672*v, 19504+913920*v)` | even/even, sum 2 mod 4 |
| q=1 | `(4932+231168*v, 26902+1260672*v)` | even/even, sum 2 mod 4 |

## 3. q=0 source-parent chain

The complete even/even parent fan forces the direct parent at sum 2 mod 4. Then the exact even/odd-four and six-even-right source inverses give:

```
P0 = (19734+924672*v, 19504+913920*v)
  -> D0 = (39236+1838592*v, 9751+456960*v)
  -> Q0 = (24491+1147776*v, 17120+802368*v)
  -> R0 = (41609+1950144*v, 8559+401184*v)
  -> S0 = (25082+1175664*v, 16819+788424*v).
```

The exact gates are:

- `P0` is even/even with sum 2 mod 4, so only its direct parent `D0` remains.
- `D0` is even/odd and `D0.x + D0.y + 1 = 4 (mod 8)`, so its even/odd-four parent is unique and is `Q0`.
- `Q0.y` is even and `Q0.x+Q0.y = 3 (mod 8)`, so the six-even-right theorem forces the direct parent `R0`.
- `R0` is odd/odd and its sum is 8 mod 16, so the odd/odd valuation-three parent is unique and is `S0`.
- `S0` has odd right coordinate and sum 1 mod 4, an established blank-image exclusion.

Hence the q=0 parent cannot be blank-reachable.

## 4. q=1 source-parent chain

The q=1 parent also has even/even sum 2 mod 4. Two applications of the direct-parent reduction, followed by the new sum-4-mod-8 direct-parent lemma, give:

```
P1 = (4932+231168*v, 26902+1260672*v)
  -> D1 = (31832+1491840*v, 13450+630336*v)
  -> D2 = (45280+2122176*v, 6724+315168*v)
  -> D3 = (52002+2437344*v, 3361+157584*v)
  -> Q3 = (27679+1297464*v, 15519+727524*v).
```

Here `D2` is even/even with sum 4 mod 8. In the complete even/even source-parent fan, both the zero-left and even-a bounce alternatives have sums divisible by 8, so only the direct parent `D3` can occur. The state `D3` is even/odd with sum-plus-one 4 mod 8, hence its even/odd-four parent is uniquely `Q3`. Finally `Q3` is odd/odd with sum 2 mod 4, another established blank-image exclusion.

Hence the q=1 parent cannot be blank-reachable either. Together with q>=2 impossibility, this proves the source-only exclusion of `X_t=(44*t-1,42*t-1)` on this entire cylinder, conditional only on the exact parent-fan and source-image lemmas already named in the Lean dependency closure.

## 5. End-to-end high-stop consequence

`U5SourceOnlyHighStopW1021.lean` lifts the new q=0 exclusion through the existing exact U5 M8 six-even-right terminal chain and the original m=0 feeder:

```
high m=0 root -> A_s -> L_s or B_s
L_s: excluded by the mod-8 image invariant
B_s: exact six-even-right chain -> terminal y=3
terminal y=3: q=0 excluded above; q=1 odd-right sum two; q>=2 contradicts m+1=1 (mod 8).
```

The existing nonemptiness theorem supplies `s,m` for every natural `w`, so this gives an infinite nonempty sequence `w=1024*n+1021` of authentic blank-unreachable high m=0 roots.

The root parameter remains `j=39+64*s = 18791 (mod 32768)`, the same containing residue as the earlier w=21 and w=37 constructions. This is an additional residual-parameter cylinder, **not** a new root-index arithmetic-progression exclusion or a density increment. The root indices grow exponentially along the sequence.

## 6. Files and verification boundary

- `U5Q0SourceOnlyW1021.lean`: exact q=0/q=1 parent-chain draft.
- `U5SourceOnlyHighStopW1021.lean`: residual lift and end-to-end high-stop draft.
- `U5Q0SourceOnly.lean` and `U5SourceOnlyHighStop.lean`: the earlier t=19 (mod 32), t=99 (mod 128), and w=21 (mod 32) source-only drafts.

No complete module in this directory has yet passed the required exact-source Lean 4.36.0-rc2 preflight and exported `#print axioms` audit. A previous invocation compiled only isolated arithmetic fragments; this invocation's local shell and Python tools returned a tool-level `ClientError`. No CI was dispatched. Agent 24 has been asked to compile the exact complete transitive source closure, including the two new files, if its local runtime is available.

Do not describe these new theorems as source-certified until the exact closure compiles and the axiom audit succeeds. Keep this material in `im-results/`; no `results/` promotion is warranted yet.
