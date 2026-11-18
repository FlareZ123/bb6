# U5 q=0 source-only closure

**Status: Lean drafts; exact-source preflight pending.** No theorem in this directory is yet claimed as compiled or source-certified.

## Contribution

This directory develops direct original-section predecessor proofs for selected cylinders of the U5 odd/odd q-fan. The proof route replaces the finite M16 quotient dependency on these cylinders with exact source-parent reductions.

| Draft module | Mathematical scope |
|---|---|
| `U5Q0SourceOnly.lean` | `X_t=(44t-1,42t-1)` is blank-unreachable for `t=32n+19` and `t=128n+99`; provides q=0-parent wrappers for `w=21 (mod 32)` and `w=37 (mod 128)`. |
| `U5SourceOnlyHighStop.lean` | Composes the `w=21 (mod 32)` q=0 exclusion with the exact M8 terminal chain and original m=0 feeder, yielding an infinite sparse high-root family. |
| `U5Q0SourceOnlyW1021.lean` | Three source-only exclusions of `X_t`: the stronger `t=459+1024v` theorem (subsuming the older `z=2 (mod 128)` wrapper), `t=123+168*(128v+126)`, and `t=123+168*(512v+193)`. |
| `U5SourceOnlyHighStopW1021.lean` | Lifts all three new q-fan closures to authentic high m=0 roots for `w=1024n+1021`, `w=1024n+413`, and `w=4096n+1125`. |
| `W1021-derivation.md` | Full arithmetic and predecessor-chain derivation of the `w=1021 (mod 1024)` cylinder. |
| `W1125-derivation.md` | Full arithmetic and predecessor-chain derivation of the `w=1125 (mod 4096)` cylinder. |
| `W413-derivation.md` | Full arithmetic and predecessor-chain derivation of the `w=413 (mod 1024)` cylinder. |

The w=1021, w=413, and w=1125 cylinders are pairwise disjoint and disjoint from the earlier w=21 (mod 32) and w=37 (mod 128) cylinders. Both remain inside the same containing root-index class `j=18791 (mod 32768)`; no density increment is claimed.

## Existing t=19 and t=99 source-only fan closures

For `t=32n+19`, the fan equation `43t-1=4^q U`, with `U` even, and `(43t-1) mod 32=16` force `q≤1`.

- At `q=0`, the parent is `(1376n+814,1360n+804)`, an even/even state with sum 2 mod 4. The complete source-parent fan leaves only its direct parent `(2736n+1616,680n+401)`, which has odd right coordinate and sum 1 mod 4.
- At `q=1`, the parent is `(344n+202,1876n+1107)`, which itself has odd right coordinate and sum 1 mod 4.

For `t=128n+99`, `(43t-1) mod 64=32` forces `q≤2`.

- At `q=0`, the even/even sum-two parent reduces to a forbidden odd-right sum-one state: `(10944n+8456,2720n+2101)`.
- At `q=1`, the parent `(1376n+1062,7504n+5797)` has a unique original-source parent `(4440n+3427,5972n+4611)`, which is odd/odd with sum 2 mod 4.
- At `q=2`, the parent `(344n+264,8020n+6193)` is odd-right with sum 1 mod 4.

The two residual wrappers reuse exact congruences derived from the U5 equations: `t=19 (mod 32)` on `w=21 (mod 32)`, and `t=99 (mod 128)` on `w=37 (mod 128)`. The exact two-step pullback from `(64t+5,32t+3)` to `X_t` is retained.

## New source-only cylinder: w=1021 (mod 1024)

The residual identity
```
211*t + 1360 + 22155*w = 20*2^(201+3360*w)
```
shows that `w=1021 (mod 1024)` forces `t=459 (mod 1024)`. The same identity also gives `t=123 (mod 168)` and the older `z=2 (mod 128)` parameterization, but the generalized q-fan proof now needs only `t=459 (mod 1024)`.

For t=459+1024v, the q-fan equation has only q=0 or q=1, because
`43t-1=19736+44032v=8 (mod 16)`. Both branches have exact finite source-parent closures:

- **q=0:** `P0=(19734+44032v,19504+43520v)` is even/even with sum 2 mod 4. Its forced direct parent is `D0=(39236+87552v,9751+21760v)`; the even/odd-four inverse gives `Q0=(24491+54656v,17120+38208v)`; six-even-right gives `R0=(41609+92864v,8559+19104v)`; odd/odd valuation three gives `S0=(25082+55984v,16819+37544v)`, odd-right with sum 1 mod 4.
- **q=1:** `P1=(4932+11008v,26902+60032v)` is even/even with sum 2 mod 4. Two direct parents give `D1=(31832+71040v,13450+30016v)` and `D2=(45280+101056v,6724+15008v)`; the sum-4-mod-8 direct-parent lemma gives `D3=(52002+116064v,3361+7504v)`; the even/odd-four inverse gives `Q3=(27679+61784v,15519+34644v)`, odd/odd with sum 2 mod 4.

The older z=2 (mod 128) statement is retained as a corollary. The full coordinates and derivations are in [W1021-derivation.md](W1021-derivation.md). These are exact source-parent arguments, not finite quotient checks.

## New source-only cylinder: w=1125 (mod 4096)

The same exact residual identity gives a second, deeper lift. If `w=1125 (mod 4096)`, then the right side is divisible by 4096 and
```
211*3875 + 1360 + 22155*1125 = 4096*6285
211*1883 = 4096*97 + 1.
```
Thus `t=3875 (mod 4096)`. Modulo 3, 7, and 8 the identity again gives `t=123 (mod 168)`, so `t=123+168z` with `z=193 (mod 512)`.

For `z=512v+193`, write `B=661+903z=174940+462336v=12 (mod 16)`. Since the q-fan condition for q≥3 requires `16 | B`, only q=0,1,2 remain. Their complete source-parent chains are:

- **q=0:** `P0=(1399518+3698688v,1383244+3655680v)` is even/even with sum 2 mod 4. Its forced direct parent `D0=(2782760+7354368v,691621+1827840v)` has odd right coordinate and sum 1 mod 4.
- **q=1:** `P1=(349878+924672v,1908061+5042688v)` is even/odd with sum-plus-one 4 mod 8. The even/odd-four inverse gives odd/odd `Q1=(1128967+2983680v,1518513+4013184v)`, sum 8 mod 16. Odd/odd valuation three gives even/even `R1=(1323738+3498432v,1421124+3755808v)`, sum 2 mod 4. Its forced direct parent `D1=(2744860+7254240v,710561+1877904v)` has odd right coordinate and sum 1 mod 4.
- **q=2:** `P2=(87468+231168v,2039263+5389440v)` is even/odd with sum-plus-one 4 mod 8. Its even/odd-four parent `Q2=(1063363+2810304v,1551312+4099872v)` is odd/even with sum 3 mod 8, so six-even-right forces `R2=(2614673+6910176v,775655+2049936v)`. This is odd/odd with sum 8 mod 16; valuation three gives `S2=(1695162+4480056v,1235407+3264996v)`, odd-right with sum 1 mod 4.

Thus all q branches terminate in established blank-image exclusions. The end-to-end high-stop theorem excludes every residual root in `w=4096n+1125`. This is a source-only subcylinder of the previously computationally identified `w=101 (mod 128)` candidate; it does not certify that entire broader cylinder. The full arithmetic is in [W1125-derivation.md](W1125-derivation.md).

## New source-only cylinder: w=413 (mod 1024)

For `w=413 (mod 1024)`, the exact residual identity gives `t=811 (mod 1024)`. Together with the invariant `t=123 (mod 168)`, this forces `z=126 (mod 128)`, so `t=123+168*(128v+126)`.

Here `B=661+903z` is odd, and `43t-1=8 (mod 16)`; hence q≥2 is impossible and only q=0,1 remain. The source-parent chains are:

- **q=0:** even/even sum-two direct parent `P0 -> D0`, then even/odd-four `D0 -> Q0`, followed by four six-even-right inverses `Q0 -> R0 -> S0 -> T0 -> U0`. The terminal `U0=(2625913+2652216v,49649+50148v)` is odd/odd with sum 2 mod 4, so blank-unreachable.
- **q=1:** even/even sum-two direct parent `P1 -> D1`, then the sum-4-mod-8 direct-parent lemma `D1 -> D2`. The terminal `D2=(2101138+2122176v,312043+315168v)` has odd right coordinate and sum 1 mod 4.

The complete affine coordinates and exact modular gates are in [W413-derivation.md](W413-derivation.md). The high-stop wrapper excludes every residual root in `w=1024n+413`.

## End-to-end high-stop root connection

`U5SourceOnlyHighStop.lean` composes the w=21 (mod 32) q=0 closure with the existing exact U5 six-even-right chain and the original `mzero_first_two_reach` / `m0_odd_ray_parent` source-parent lemmas. Its main draft theorem is `blank_no_high_m0_u5_w21`.

`U5SourceOnlyHighStopW1021.lean` gives `blank_no_high_m0_u5_w1021` for `w=1021 (mod 1024)`, `blank_no_high_m0_u5_w413` for `w=413 (mod 1024)`, and `blank_no_high_m0_u5_w1125` for `w=1125 (mod 4096)`. These use respectively the t=459 (mod1024) q=0/1, z=126 (mod128) q=0/1, and z=193 (mod512) q=0/1/2 closures. Both are composed with the exact M8 terminal and m=0 feeder.

The earlier high-stop file also drafts `u5_residual_nonempty`: for every natural w it constructs natural s,m satisfying the two residual equations. It uses `2^210 ≡ 1 (mod 211)`, `2^201 ≡ 68 (mod 211)`, and `2^r ≥ r+1` to obtain `s ≥ 27w+1` and `m ≥ 24w`. The theorem `u5_residual_s_strict_mono` proves s is strictly increasing with w for any two residual solutions. Consequently, `every_w1021_residual_has_unreachable_root`, `every_w413_residual_has_unreachable_root`, and `every_w1125_residual_has_unreachable_root` package w=1024n+1021, w=1024n+413, and w=4096n+1125 as explicit infinite sequences of nonempty residual instances whose high m=0 roots are excluded.

Every such residual has `s=293 (mod 512)`, hence the stopping-root index `j=39+64s` satisfies `j=18791 (mod 32768)`, equivalently `(j-7)/32=587 (mod 1024)`. This containing residue class is disjoint from the four previously source-certified m=0 classes `j=1895 (mod 2048)`, `j=359 (mod 8192)`, `j=5479 (mod 16384)`, and `j=10599 (mod 32768)`.

**Density qualification:** the residual equations generate only exponentially sparse sequences of root indices, not every index in `j=18791 (mod 32768)`. The w=1021, w=413, and w=1125 cylinders are additional infinite parameter subfamilies within the same containing root residue; they are not new root-index arithmetic-progression exclusions and no density increment is claimed. The existing 23/512 coverage is unchanged.

## Verification and next steps

A previous invocation locally compiled only isolated arithmetic declarations from `U5SourceOnlyHighStop.lean` (`u5_residual_nonempty`, `u5_residual_s_strict_mono`, and `u5_high_root_parameter_residue`) and audited their axioms. This did **not** compile either complete source-only module or certify the parent/root chain.

The complete source closure remains uncompiled and no CI was dispatched, respecting the focused-local-preflight-before-CI instruction. Agent 24 has been asked to preflight the latest W1021 source modules together with the W413/W1125 theorem families using Lean 4.36.0-rc2 if its local runtime is available.

The exact closure must include at least `U5Q0OddOddFan`, `U5Y3ParentFan`, `U5Y3M8`, `U5M8Q0Partial`, `U5Q0M16Residual`, `EvenEvenParentFan`, `EvenOddFourExact`, `OddOddVal3Orbit`, `EvenRightSixOrbit`, `M0EvenEvenSumZero`, `HighSumTwo`, and all original-section/source-image imports. After a successful compile, inspect `#print axioms` for every exported declaration. Only then consider a focused manual source workflow and possible promotion of any genuinely publishable result. Until then, all four Lean files remain drafts under `im-results/`; `results/` is unchanged.
