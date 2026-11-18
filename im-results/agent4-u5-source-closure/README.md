# U5 q=0 source-only closure

**Status: Lean drafts; exact-source preflight pending.** No theorem in this directory is yet claimed as compiled or source-certified.

## Contribution

This directory develops direct original-section predecessor proofs for selected cylinders of the U5 odd/odd q-fan. The proof route replaces the finite M16 quotient dependency on these cylinders with exact source-parent reductions.

| Draft module | Mathematical scope |
|---|---|
| `U5Q0SourceOnly.lean` | `X_t=(44t-1,42t-1)` is blank-unreachable for `t=32n+19` and `t=128n+99`; provides q=0-parent wrappers for `w=21 (mod 32)` and `w=37 (mod 128)`. |
| `U5SourceOnlyHighStop.lean` | Composes the `w=21 (mod 32)` q=0 exclusion with the exact M8 terminal chain and original m=0 feeder, yielding an infinite sparse high-root family. |
| `U5Q0SourceOnlyW1021.lean` | Five generalized source-only exclusions of `X_t`: `t=459+1024v`, `t=811+1024v`, `t=3875+4096v`, `t=1707+2048v`, and the new `t=1547+2048v`; the older z-parameter statements remain as corollaries. |
| `U5SourceOnlyHighStopW1021.lean` | Lifts the generalized q-fan closures to authentic high m=0 roots for `w=1024n+1021`, `w=1024n+413`, `w=4096n+1125`, `w=2048n+541`, and the new `w=2048n+445`. |
| `W1021-derivation.md` | Full arithmetic and predecessor-chain derivation of the `w=1021 (mod 1024)` cylinder. |
| `W1125-derivation.md` | Full arithmetic and predecessor-chain derivation of the `w=1125 (mod 4096)` cylinder. |
| `W413-derivation.md` | Full arithmetic and predecessor-chain derivation of the `w=413 (mod 1024)` cylinder. |
| `W51741-derivation.md` | Consolidated derivation of the widened `w=541 (mod 2048)` and sum-seven `w=445 (mod 2048)` cylinders. |
| `W541W445Arithmetic.lean` | Standalone Lean 4.36.0-rc2 check of all affine parent equations and modular gate residues for both cylinders; does not certify source-predecessor imports. |

The w=1021, w=413, w=1125, w=541, and w=445 cylinders are pairwise disjoint and disjoint from the earlier w=21 (mod 32) and w=37 (mod 128) cylinders. The narrower w=51741 (mod 65536) class is contained in w=541 (mod 2048). Both remain inside the same containing root-index class `j=18791 (mod 32768)`; no density increment is claimed.

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

The exact residual identity

    211*t + 1360 + 22155*w = 20*2^(201+3360*w)

and

    211*3875 + 1360 + 22155*1125 = 4096*6285
    211*1883 = 4096*97 + 1

show directly that w=1125 (mod 4096) forces t=3875 (mod 4096). The older CRT calculation also gives z=193 (mod 512), but the generalized q-fan proof needs only the t residue.

For t=3875+4096v, 43t-1=166624+176128v=96 (mod 128), so q≥3 is impossible. The three remaining source-parent branches are:

- **q=0:** P0=(166622+176128v,164684+174080v) is even/even with sum 2 mod 4. Its forced direct parent D0=(331304+350208v,82341+87040v) has odd right coordinate and sum 1 mod 4.
- **q=1:** P1=(41654+44032v,227165+240128v) is even/odd with sum-plus-one 4 mod 8. The even/odd-four inverse gives Q1=(134407+142080v,180785+191104v), odd/odd with sum 8 mod 16. Odd/odd valuation three gives R1=(157594+166592v,169188+178848v), even/even with sum 2 mod 4. Its forced direct parent D1=(326780+345440v,84593+89424v) has odd right coordinate and sum 1 mod 4.
- **q=2:** P2=(10412+11008v,242783+256640v) is even/odd with sum-plus-one 4 mod 8. Its even/odd-four parent is Q2=(126595+133824v,184688+195232v), odd/even with sum 3 mod 8; six-even-right forces R2=(311281+329056v,92343+97616v), odd/odd with sum 8 mod 16; valuation three gives S2=(201810+213336v,147075+155476v), odd-right with sum 1 mod 4.

All q branches terminate in established blank-image exclusions. The end-to-end high-stop theorem excludes every residual root in w=4096n+1125. This is a source-only subcylinder of the previously computationally identified w=101 (mod 128) candidate; it does not certify that entire broader cylinder. The full derivation is in [W1125-derivation.md](W1125-derivation.md).

## New source-only cylinder: w=413 (mod 1024)

The exact residual identity and

    211*811 + 1360 + 22155*413 = 1024*9104
    211*859 = 1024*177 + 1

show directly that w=413 (mod 1024) forces t=811 (mod 1024). The older CRT calculation also gives z=126 (mod 128), but the generalized q-fan proof needs only the t residue.

For t=811+1024v, 43t-1=34872+44032v=8 (mod 16), so q≥2 is impossible. The source-parent chains are:

- **q=0:** even/even sum-two direct parent P0=(34870+44032v,34464+43520v) gives D0=(69332+87552v,17231+21760v); the even/odd-four inverse gives Q0=(43279+54656v,30254+38208v); four six-even-right inverses give R0=(73531+92864v,15126+19104v), S0=(88655+111968v,7562+9552v), T0=(96215+121520v,3780+4776v), and U0=(99993+126296v,1889+2388v). U0 is odd/odd with sum 2 mod 4.
- **q=1:** even/even sum-two direct parent P1=(8716+11008v,47538+60032v) gives D1=(56252+71040v,23768+30016v). D1 is even/even with sum 4 mod 8, so the sum-4-mod-8 direct-parent lemma gives D2=(80018+101056v,11883+15008v), odd-right with sum 1 mod 4.

The complete affine coordinates and exact modular gates are in [W413-derivation.md](W413-derivation.md). The high-stop wrapper excludes every residual root in w=1024n+413.

## New source-only cylinder: w=541 (mod 2048)

The exact residual identity

\[
211t+1360+22155w=20\cdot 2^{201+3360w}
\]

and the arithmetic

\[
211\cdot1707+1360+22155\cdot541=2048\cdot6029,\qquad
211\cdot22363=2048\cdot2304+1
\]

show that w=541 (mod 2048) forces t=1707 (mod 2048). Write
t=1707+2048v. Then 43t-1=73400+43\cdot2048v is 8 modulo 16, so
the exact q-fan has only q=0 or q=1.

The two source-parent branches both terminate in the established odd-image
forbidden class:

- **q=0:** the fan parent
  P0=(73398+88064v,72544+87040v) is even/even with sum 2 mod 4.
  Its forced direct parent is
  D0=(145940+175104v,36271+43520v), even/odd with
  (x+y+1)=4 (mod 8). The unique even/odd-four parent is
  Q0=(91103+109312v,63686+76416v). Three exact six-even-right
  inverses give
  R1=(154787+185728v,31842+38208v),
  R2=(186627+223936v,15920+19104v), and
  R3=(202545+243040v,7959+9552v). Here R3 is odd/odd with
  sum 8 mod 16; its unique valuation-three parent is
  S0=(105250+126296v,56603+67924v), odd-right with sum 1 mod 4.
- **q=1:** the fan parent
  P1=(18348+22016v,100066+120064v) is even/even with sum 2 mod 4.
  Its forced direct parent is
  D1=(118412+142080v,50032+60032v), even/even with sum 4 mod 8.
  The forced direct parent
  D2=(168442+202112v,25015+30016v) is odd-right with sum 1 mod 4.

Thus X_t is blank-unreachable for every t=1707+2048v. Composing this
with the existing M8 terminal and original m=0 feeder proves an infinite
nonempty high-stop root sequence for w=2048n+541. Its root index
remains j=18791 (mod 32768), so this is a further parameter cylinder
inside the existing containing root residue, not a new root-index
arithmetic-progression exclusion or a density increment. It contains the
previously explored w=51741 (mod 65536) subcylinder and is disjoint
from the other previously listed w-cylinders.

The Lean declarations have been widened in the existing W1021 source
modules. They remain uncompiled drafts; no exact-source certification or
BB(6) conclusion is claimed.

## Second source-only cylinder: w=445 (mod 2048)

The residual identity and exact constants

\[
211\cdot1547+1360+22155\cdot445=2048\cdot4974,\qquad
211\cdot22363=2048\cdot2304+1
\]

show that w=445 (mod 2048) forces t=1547 (mod 2048). Write
t=1547+2048v. Again, 43t-1 is 8 modulo 16, so only q=0,1 occur.

- **q=0:** the fan parent
  P0=(66518+88064v,65744+87040v) is even/even with sum 2 mod 4.
  Its forced direct parent is
  D0=(132260+175104v,32871+43520v), even/odd with
  x+y+1=4 (mod 8). The even/odd-four inverse gives
  Q0=(82563+109312v,57716+76416v). This target satisfies the exact
  sum-seven cylinder: y>=12, x+y=7 (mod 8), x+y+1=8 (mod 16),
  x+y+1=24 (mod 32), x=3 (mod 4), and y=4 (mod 8).
  The source-complete sum-seven parent theorem therefore sends every
  possible parent to an odd/odd sum-two state, which is blank-unreachable.
- **q=1:** the fan parent
  P1=(16628+22016v,90686+120064v) is even/even with sum 2 mod 4.
  Six forced even/even direct inverses give
  D1=(107312+142080v,45342+60032v),
  D2=(152652+202112v,22670+30016v),
  D3=(175320+232128v,11334+15008v),
  D4=(186652+247136v,5666+7504v),
  D5=(192316+254640v,2832+3752v), and
  D6=(195146+258392v,1415+1876v).
  The first five direct steps use the sum-two-mod-four inverse; the
  final step uses the even/even sum-four-mod-eight inverse. D6 is
  odd-right with sum 1 mod 4, hence blank-unreachable.

Both q branches are excluded, giving X_t unreachable for every
t=1547+2048v. The same M8 terminal and original m=0 feeder then prove
an infinite nonempty high-stop root sequence for w=2048n+445, again
with j=18791 (mod 32768). This is a distinct parameter cylinder from
w=541 (mod 2048), not a new root-index progression or density increment.

The q=0 branch uses Agent 19's exact sum-seven parent theorem; it does
not use a finite quotient. The declarations are still uncompiled drafts.

## End-to-end high-stop root connection

`U5SourceOnlyHighStop.lean` composes the w=21 (mod 32) q=0 closure with the existing exact U5 six-even-right chain and the original `mzero_first_two_reach` / `m0_odd_ray_parent` source-parent lemmas. Its main draft theorem is `blank_no_high_m0_u5_w21`.

`U5SourceOnlyHighStopW1021.lean` gives `blank_no_high_m0_u5_w1021` for `w=1021 (mod 1024)`, `blank_no_high_m0_u5_w413` for `w=413 (mod 1024)`, and `blank_no_high_m0_u5_w1125` for `w=1125 (mod 4096)`. These use respectively the generalized t=459 (mod1024), t=811 (mod1024), and t=3875 (mod4096) q-fan closures. Both are composed with the exact M8 terminal and m=0 feeder.

The earlier high-stop file also drafts `u5_residual_nonempty`: for every natural w it constructs natural s,m satisfying the two residual equations. It uses `2^210 ≡ 1 (mod 211)`, `2^201 ≡ 68 (mod 211)`, and `2^r ≥ r+1` to obtain `s ≥ 27w+1` and `m ≥ 24w`. The theorem `u5_residual_s_strict_mono` proves s is strictly increasing with w for any two residual solutions. Consequently, `every_w1021_residual_has_unreachable_root`, `every_w413_residual_has_unreachable_root`, and `every_w1125_residual_has_unreachable_root` package w=1024n+1021, w=1024n+413, and w=4096n+1125 as explicit infinite sequences of nonempty residual instances whose high m=0 roots are excluded.

Writing `j=39+64s`, the exact residual equation gives `211*j+27=320*2^(201+3360*w)`. Since 32768 divides the right side and `211*22363=32768*144+1`, we obtain `j=18791 (mod 32768)`; because `j=7+32*(1+2s)`, this also gives `1+2s=587 (mod 1024)` (equivalently `s=293 (mod 512)`). This containing residue class is disjoint from the four previously source-certified m=0 classes `j=1895 (mod 2048)`, `j=359 (mod 8192)`, `j=5479 (mod 16384)`, and `j=10599 (mod 32768)`.

**Density qualification:** the residual equations generate only exponentially sparse sequences of root indices, not every index in `j=18791 (mod 32768)`. The w=1021, w=413, and w=1125 cylinders are additional infinite parameter subfamilies within the same containing root residue; they are not new root-index arithmetic-progression exclusions and no density increment is claimed. The existing 23/512 coverage is unchanged.

## Verification and next steps

A previous invocation locally compiled only isolated arithmetic declarations from `U5SourceOnlyHighStop.lean` (`u5_residual_nonempty`, `u5_residual_s_strict_mono`, and `u5_high_root_parameter_residue`) and audited their axioms. This did **not** compile either complete source-only module or certify the parent/root chain.

The standalone arithmetic file W541W445Arithmetic.lean compiles with Lean 4.36.0-rc2. The complete exact-source closure, including the W541 and W445 declarations and the added HighEvenRightSum7Source/HighSumTwo imports, remains uncompiled; no CI has been dispatched. The next useful check is one focused Lean 4.36.0-rc2 preflight of the complete transitive imports, followed by #print axioms for every exported declaration. Until that succeeds, all files remain drafts under im-results/ and results/ is unchanged.

The exact closure must include at least `U5Q0OddOddFan`, `U5Y3ParentFan`, `U5Y3M8`, `U5M8Q0Partial`, `U5Q0M16Residual`, `EvenEvenParentFan`, `EvenOddFourExact`, `OddOddVal3Orbit`, `EvenRightSixOrbit`, `M0EvenEvenSumZero`, `HighSumTwo`, and all original-section/source-image imports. After a successful compile, inspect `#print axioms` for every exported declaration. Only then consider a focused manual source workflow and possible promotion of any genuinely publishable result. Until then, all four Lean files remain drafts under `im-results/`; `results/` is unchanged.
