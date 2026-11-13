# Root119: ten-million-step B/0 interval macro closure audit

**Status: finite computational classification; not an all-time theorem.** This note records a new 10,000,000-transition replay of the auxiliary machine
`1RB---_1LC1LF_1LD0LC_0LE1RF_1RA1LA_1LB0RD`. The replay found 22,984 B/0 sections and 22,983 consecutive B/0-to-B/0 intervals. Every interval matched one of the existing source-derived return families or three residual families described below; no unmatched interval remained in this bounded run.

The replay was executed in the current invocation's JavaScript runtime using a separate sparse/typed-tape implementation of the literal twelve-rule table. The repository's `test-root119-two-wave-census.cjs` has now been extended with the three residual detectors, exact return-time/head assertions, parameter histograms, and a zero-unmatched expectation. That modified repository script has **not yet been run in Node/CI**.

## Complete bounded partition

| Return family | Intervals | Exact local return law |
|---|---:|---|
| Original odd F/1 wave | 7,508 | `4n+5` steps; head `h-1` |
| Left-one odd F/1 wave | 177 | `4n+7` steps; head `h-3` |
| Even-prefix B/0 return | 21 | `m+13` steps; head `h+m+1` |
| Odd-even-prefix B/0 return | 22 | `3m+20` steps; head `h+m+2` |
| Two-wave-root return | 8 | `8n₁+2r+30` steps; head `h-2r-6` |
| C-phase D1 return | 15,198 | `r+7` steps; head `h-r+1` |
| Zero-left even-run return | 18 | `2n+12` steps; head `h+2n+2` |
| C-phase D0 / odd F1 wave / retreat | 29 | `r+2m+13` steps; head `h-r-7-2m` |
| C0/D1 odd shuttle / retreat | 2 | `4n+2m+8` steps; head `h-6-2m` |
| Unmatched / other | **0** | — |
| **Total** | **22,983** | |

The first six families are the established census classes. The three additional families account for all 49 formerly residual intervals (18 + 29 + 2). The updated census script asserts that the family predicates are disjoint, each predicted endpoint agrees with the replay, the 22,983 intervals partition all consecutive B/0 sections, and the cumulative macro chain has no gap through the cutoff.

## Residual-family hypotheses and existing source theorems

### 1. Zero-left even run (18 intervals)

This is the new source theorem in `Root119ZeroLeftEvenRun.lean`, currently pending a Lean 4.36.0-rc2 compile after replacing the failed monolithic simplification with eight explicit transition lemmas.

At a B/0 head (h), require:
- (t(h-1)=t(h-2)=t(h-3)=0);
- (t(h+1),\ldots,t(h+2n)=1);
- (t(h+2n+1)=t(h+2n+2)=0).

Then the intended exact theorem `zeroLeftEvenRun_exact` returns B/0 at (h+2n+2) after (2n+12) primitive steps, with the complete output tape specified in the Lean source. The 18 replay parameters are
`n = 3, 5, 6, 6, 45, 74, 93, 94, 107, 137, 171, 173, 176, 274, 302, 345, 442, 684`.

### 2. C-phase D0 / odd F1 wave / alternating retreat (29 intervals)

These intervals instantiate the existing theorem
`b0_cphase_d0_odd_wave_return` in `Root119OddWaveRetreat.lean`, with the odd F1 wave parameter (n=0). The local hypotheses are:
- a left scan of (r) ones;
- then the pattern (0,0,1,0,1);
- then (m) repetitions of (0,1);
- then the two zero sentinels required by the retreat theorem.

The exact return is (r+2m+13) steps at (h-r-7-2m). The replay splits as **19 cases with (r=3)** and **10 cases with (r=1)**. These are the former `leftSix=100111` and `leftSix=101001` residuals, respectively.

### 3. C0/D1 odd shuttle / alternating retreat (2 intervals)

These instantiate the existing theorem
`b0_c0_d1_odd_retreat_to_b0` in `Root119OddWaveRetreat.lean`. The local left pattern begins (0,1,0,1); after the B0-C0-D1 prefix, the rightward D1 shuttle has odd length (2n+1), followed by the theorem's alternating retreat of (m) pairs. The exact return is (4n+2m+8) steps at (h-6-2m). The two replay parameter pairs are ((n,m)=(17,6)) and ((369,25)), matching the former `leftSix=101010` cases.

## Research consequence and limits

The 10M replay no longer exhibits a gap in its B/0 first-return classification. In particular, the eight two-wave-root intervals that previously followed an unclassified prefix are now preceded by a fully classified sequence in the bounded replay. The updated script therefore expects all eight to have `chainKnown` rather than `chainUnknown`.

This is **not** yet a formal Lean proof that all 22,984 B/0 configurations are reached from blank:
- the new `zeroLeftEvenRun_exact` proof patch is not compile-verified;
- the updated census script is not yet run in Node/CI;
- the finite replay's macro predicates and parameter checks are computational evidence, not a Lean certificate of the entire 10M-step history;
- even a formally certified 10M prefix would not establish an all-time invariant or decide the blank-root machine.

The next useful step is to compile the zero-left macro, run the extended census in the existing manual-only workflow, then construct a compact source-level certificate for the finite macro chain. The larger mathematical obligation remains an inductive all-time reachable B/0 language excluding the stopping gate, or a genuine reached gate witness. No BB(6) value or universal six-state upper bound follows from this audit.
