# Source-only closure on the U5 residual cylinder w = 413 (mod 1024)

**Status: exact arithmetic derivation and Lean draft; not yet compiled or source-certified.** This remains intermediate work under `im-results/`.

## 1. Residual lift

The exact residual identity is

```
211*t + 1360 + 22155*w = 20*2^(201+3360*w).
```

For `w=413+1024*n`, the right side is divisible by 1024, and

```
211*811 + 1360 + 22155*413 = 1024*9104
211*859 = 1024*177 + 1.
```

Therefore `t=811 (mod 1024)`. Modulo 3, 7, and 8 the same identity gives `t=0 (mod3)`, `t=4 (mod7)`, and `t=3 (mod8)`, hence `t=123 (mod168)`. Write `t=123+168z`. Combining with `t=811 (mod1024)` yields `z=126 (mod128)`, since `21*61=128*10+1`.

Thus

```
t = 123 + 168*(128*v+126).
```

## 2. Exact q-fan depth

For `z=128*v+126`, `B=661+903*z` is odd and

```
43*t-1 = 915512 + 924672*v = 8 (mod 16).
```

The q-fan equation is `43*t-1=4^q*U` with `U` even. If `q>=2`, then `16 | 4^q*U`, contradicting the residue 8 mod 16. Thus q is 0 or 1.

## 3. q=0 source-parent chain

```
P0 = (915510+924672*v, 904864+913920*v)
  -> D0 = (1820372+1838592*v, 452431+456960*v)
  -> Q0 = (1136399+1147776*v, 794414+802368*v)
  -> R0 = (1930811+1950144*v, 397206+401184*v)
  -> S0 = (2328015+2351328*v, 198602+200592*v)
  -> T0 = (2526615+2551920*v, 99300+100296*v)
  -> U0 = (2625913+2652216*v, 49649+50148*v).
```

- `P0` is even/even with sum 2 mod 4, so only the direct parent `D0` is possible.
- `D0` is even/odd with sum-plus-one 4 mod 8, so its even/odd-four parent is uniquely `Q0`.
- `Q0,R0,S0,T0` are odd/even with sums respectively 5,1,1,3 mod 8, so six-even-right forces each next direct parent.
- `U0` has odd right coordinate and sum 2 mod 4, an established blank-image exclusion.

## 4. q=1 source-parent chain

```
P1 = (228876+231168*v, 1248178+1260672*v)
  -> D1 = (1477052+1491840*v, 624088+630336*v)
  -> D2 = (2101138+2122176*v, 312043+315168*v).
```

- `P1` is even/even with sum 2 mod 4, so its direct parent is forced.
- `D1` is even/even with sum 4 mod 8, so the complete source parent fan forces the direct parent `D2`; the zero-left and bounce alternatives have sums divisible by 8.
- `D2` has odd right coordinate and sum 1 mod 4, so it is not blank-reachable.

All q branches are therefore excluded by exact original-source predecessor lemmas. The Lean theorem is `q0_X_not_reach_t123_z126mod128`.

## 5. High-stop consequence and scope

The exact U5 M8 terminal and original m=0 feeder lift this to `blank_no_high_m0_u5_w413` and `every_w413_residual_has_unreachable_root` for every `w=1024*n+413`. The stopping-root index remains `j=39+64*s=18791 (mod32768)`, the same containing class as the W21, W1021, and W1125 families. This is a sparse residual parameter sequence, not a new root-index arithmetic progression or density increment.

## 6. Verification boundary

The proof is currently a Lean draft in `U5Q0SourceOnlyW1021.lean` and `U5SourceOnlyHighStopW1021.lean`. No full Lean 4.36.0-rc2 transitive compile or exported axiom audit has succeeded. Keep it in `im-results/`; do not describe it as source-certified or promote it to `results/` until exact compilation and the axiom audit pass.
