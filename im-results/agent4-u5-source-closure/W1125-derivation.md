# Source-only closure on the U5 residual cylinder w = 1125 (mod 4096)

**Status: exact arithmetic derivation and Lean draft; not yet compiled or source-certified.** This is intermediate work under `im-results/`.

## 1. Residual lift

The exact residual pullback identity is

```
211*t + 1360 + 22155*w = 20*2^(201+3360*w).
```

For `w=1125+4096*n`, the right side is divisible by 4096, and

```
211*3875 + 1360 + 22155*1125 = 4096*6285
211*1883 = 4096*97 + 1.
```

Hence `t=3875 (mod 4096)`. Modulo 3, 7, and 8 the same identity gives `t=0 (mod 3)`, `t=4 (mod 7)`, and `t=3 (mod 8)`, so `t=123 (mod 168)`. Write `t=123+168*z`. Combining this with `t=3875 (mod 4096)` gives `z=193 (mod 512)`, using `21*317=512*13+1`.

Thus the residual cylinder maps exactly to

```
t = 123 + 168*(512*v+193).
```

## 2. Exact q-fan depth

For `z=512*v+193`,

```
B = 661+903*z = 174940+462336*v = 12 (mod 16)
43*t-1 = 8*B = 96 (mod 128).
```

The q-fan equation is `43*t-1=4^q*U` with `U` even. If `q>=3`, then `128 | 4^q*U`, contradicting the residue 96 mod 128. Therefore q is exactly one of 0, 1, or 2.

## 3. q=0 source-parent chain

```
P0 = (1399518+3698688*v, 1383244+3655680*v)
  -> D0 = (2782760+7354368*v, 691621+1827840*v).
```

`P0` is even/even with sum 2 mod 4, so the complete even/even parent fan forces the direct parent `D0`. The right coordinate of `D0` is odd and its sum is 1 mod 4, an established blank-image exclusion.

## 4. q=1 source-parent chain

```
P1 = (349878+924672*v, 1908061+5042688*v)
  -> Q1 = (1128967+2983680*v, 1518513+4013184*v)
  -> R1 = (1323738+3498432*v, 1421124+3755808*v)
  -> D1 = (2744860+7254240*v, 710561+1877904*v).
```

- `P1` is even/odd with sum-plus-one 4 mod 8, so the even/odd-four parent is unique and is `Q1`.
- `Q1` is odd/odd with sum 8 mod 16, so the valuation-three parent is unique and is `R1`.
- `R1` is even/even with sum 2 mod 4, so the complete even/even parent fan forces `D1`.
- `D1` has odd right coordinate and sum 1 mod 4, so it is not blank-reachable.

## 5. q=2 source-parent chain

```
P2 = (87468+231168*v, 2039263+5389440*v)
  -> Q2 = (1063363+2810304*v, 1551312+4099872*v)
  -> R2 = (2614673+6910176*v, 775655+2049936*v)
  -> S2 = (1695162+4480056*v, 1235407+3264996*v).
```

- `P2` is even/odd with sum-plus-one 4 mod 8, so its unique even/odd-four parent is `Q2`.
- `Q2` is odd/even with sum 3 mod 8, so six-even-right forces the direct parent `R2`.
- `R2` is odd/odd with sum 8 mod 16, so valuation three forces `S2`.
- `S2` has odd right coordinate and sum 1 mod 4, so it is not blank-reachable.

All q branches therefore end in established blank-image exclusions. The Lean theorem is `q0_X_not_reach_t123_z193mod512`.

## 6. High-stop consequence and scope

The existing exact U5 M8 terminal and original m=0 feeder lift this to `blank_no_high_m0_u5_w1125` and `every_w1125_residual_has_unreachable_root` for every `w=4096*n+1125`. The root index remains `j=39+64*s=18791 (mod 32768)`, the same containing class as the earlier W21 and W1021 families.

This is a source-only subcylinder of the previously computationally identified `w=101 (mod 128)` candidate. It does not establish the whole w=101 class and does not add a new root-index arithmetic progression or density claim.

## 7. Verification boundary

The proof is currently a Lean draft in `U5Q0SourceOnlyW1021.lean` and `U5SourceOnlyHighStopW1021.lean`. No full Lean 4.36.0-rc2 transitive compile or exported axiom audit has succeeded yet. Keep this under `im-results/`; do not describe it as source-certified or promote it to `results/` until exact compilation and the axiom audit pass.
