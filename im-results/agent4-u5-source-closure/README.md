# U5 q=0 source-only closure

**Status: Lean drafts; exact-source preflight pending.** No theorem in this directory is yet claimed as compiled or source-certified.

## Contribution

This directory develops direct original-section predecessor proofs for selected cylinders of the U5 odd/odd q-fan. The proof route replaces the finite M16 quotient dependency on these cylinders with exact source-parent reductions.

| Draft module | Mathematical scope |
|---|---|
| `U5Q0SourceOnly.lean` | `X_t=(44t-1,42t-1)` is blank-unreachable for `t=32n+19` and `t=128n+99`; provides q=0-parent wrappers for `w=21 (mod 32)` and `w=37 (mod 128)`. |
| `U5SourceOnlyHighStop.lean` | Composes the `w=21 (mod 32)` q=0 exclusion with the exact M8 terminal chain and original m=0 feeder, yielding an infinite sparse high-root family. |
| `U5Q0SourceOnlyW1021.lean` | New source-only exclusion of `X_t` for `t=123+168*(128v+2)`. |
| `U5SourceOnlyHighStopW1021.lean` | Lifts the new q=0/q=1 closure to the authentic high m=0 root for every `w=1024n+1021`. |
| `W1021-derivation.md` | Full arithmetic and predecessor-chain derivation of the new cylinder. |

The new w=1021 cylinder is disjoint from the earlier w=21 (mod 32) and w=37 (mod 128) cylinders. It remains inside the same containing root-index class `j=18791 (mod 32768)`; no density increment is claimed.

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
shows that `w=1021 (mod 1024)` forces `t=459 (mod 1024)`. Modulo 3, 7, and 8 it also gives `t=123 (mod 168)`; hence `t=123+168z` with `z=2 (mod 128)`.

For `z=128v+2`, the q-fan equation has only q=0 or q=1, because `43t-1=8(661+903z)=8 (mod 16)`. Both branches have exact finite source-parent closures:

- **q=0:** `P0 -> D0 -> Q0 -> R0 -> S0`. The gates are even/even sum two, even/odd-four, six-even-right, and odd/odd valuation three. The terminal `S0=(25082+2351328v,16819+1576848v)` has odd right coordinate and sum 1 mod 4.
- **q=1:** `P1 -> D1 -> D2 -> D3 -> Q3`. The first two steps are even/even sum-two direct parents; `D2` has sum 4 mod 8, so the complete source fan forces its direct parent; the even/odd-four inverse then gives `Q3=(27679+2594928v,15519+1455048v)`, odd/odd with sum 2 mod 4.

The full coordinates and derivations are in [W1021-derivation.md](W1021-derivation.md). These are exact source-parent arguments, not finite quotient checks.

## End-to-end high-stop root connection

`U5SourceOnlyHighStop.lean` composes the w=21 (mod 32) q=0 closure with the existing exact U5 six-even-right chain and the original `mzero_first_two_reach` / `m0_odd_ray_parent` source-parent lemmas. Its main draft theorem is `blank_no_high_m0_u5_w21`.

`U5SourceOnlyHighStopW1021.lean` gives the parallel theorem `blank_no_high_m0_u5_w1021`. It uses the exact q=0/q=1 source-only closure above, the q=1 odd-right sum-two exclusion, and the q≥2 contradiction from `m+1=1 (mod 8)`.

The earlier high-stop file also drafts `u5_residual_nonempty`: for every natural w it constructs natural s,m satisfying the two residual equations. It uses `2^210 ≡ 1 (mod 211)`, `2^201 ≡ 68 (mod 211)`, and `2^r ≥ r+1` to obtain `s ≥ 27w+1` and `m ≥ 24w`. The theorem `u5_residual_s_strict_mono` proves s is strictly increasing with w for any two residual solutions. Consequently, the new `every_w1021_residual_has_unreachable_root` theorem packages w=1024n+1021 as an explicit infinite sequence of nonempty residual instances whose high m=0 roots are excluded.

Every such residual has `s=293 (mod 512)`, hence the stopping-root index `j=39+64s` satisfies `j=18791 (mod 32768)`, equivalently `(j-7)/32=587 (mod 1024)`. This containing residue class is disjoint from the four previously source-certified m=0 classes `j=1895 (mod 1024)`, `j=359 (mod 8192)`, `j=5479 (mod 16384)`, and `j=10599 (mod 32768)`.

**Density qualification:** the residual equations generate only exponentially sparse sequences of root indices, not every index in `j=18791 (mod 32768)`. The new w=1021 cylinder is an additional infinite parameter subfamily within the same containing root residue; it is not a new arithmetic-progression exclusion and no density increment is claimed. The existing 23/512 coverage is unchanged.

## Verification and next steps

A previous invocation locally compiled only isolated arithmetic declarations from `U5SourceOnlyHighStop.lean` (`u5_residual_nonempty`, `u5_residual_s_strict_mono`, and `u5_high_root_parameter_residue`) and audited their axioms. This did **not** compile either complete source-only module or certify the parent/root chain.

In the current invocation, the local shell and Python execution tools failed at the tool boundary with `ClientError`. No CI was dispatched, respecting the focused-local-preflight-before-CI instruction. Agent 24 has been asked to compile the exact complete transitive closure, including both new W1021 modules, with Lean 4.36.0-rc2 if its local runtime is available.

The exact closure must include at least `U5Q0OddOddFan`, `U5Y3ParentFan`, `U5Y3M8`, `U5M8Q0Partial`, `U5Q0M16Residual`, `EvenEvenParentFan`, `EvenOddFourExact`, `OddOddVal3Orbit`, `EvenRightSixOrbit`, `M0EvenEvenSumZero`, `HighSumTwo`, and all original-section/source-image imports. After a successful compile, inspect `#print axioms` for every exported declaration. Only then consider a focused manual source workflow and possible promotion of any genuinely publishable result. Until then, all four Lean files remain drafts under `im-results/`; `results/` is unchanged.
