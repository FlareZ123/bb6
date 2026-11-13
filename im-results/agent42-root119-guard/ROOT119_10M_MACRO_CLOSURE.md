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

## Observed macro transition graph

The replay also records the family of each interval and the family of the immediately following interval. Across the 22,982 adjacent pairs of intervals, the observed edge counts are:

| Source family | Destination family | Edges |
|---|---|---:|
| oldWave | oldWave | 7,391 |
| oldWave | evenPrefix | 21 |
| oldWave | oddEvenPrefix | 19 |
| oldWave | leftOneWave | 55 |
| oldWave | twoWaveRoot | 8 |
| oldWave | cphaseD0Odd | 10 |
| oldWave | c0D1Odd | 2 |
| oldWave | cphaseD1 | 1 |
| cphaseD1 | cphaseD1 | 15,136 |
| cphaseD1 | leftOneWave | 41 |
| cphaseD1 | oldWave | 2 |
| cphaseD1 | cphaseD0Odd | 19 |
| leftOneWave | leftOneWave | 80 |
| leftOneWave | oldWave | 95 |
| leftOneWave | zeroLeftEven | 1 |
| leftOneWave | oddEvenPrefix | 1 |
| zeroLeftEven | cphaseD1 | 18 |
| evenPrefix | cphaseD1 | 21 |
| oddEvenPrefix | cphaseD1 | 22 |
| cphaseD0Odd | zeroLeftEven | 17 |
| cphaseD0Odd | oldWave | 10 |
| cphaseD0Odd | oddEvenPrefix | 2 |
| c0D1Odd | oldWave | 2 |
| twoWaveRoot | oldWave | 8 |
| **Total adjacent interval pairs** | | **22,982** |

A second pass checked parameter relations on every observed edge; it found no violations of the following finite-run rules:

- `oldWave(n) → oldWave(2)` or `oldWave(n+4)`;
- `oldWave(n) → evenPrefix(2n+4)` or `oddEvenPrefix(2n+5)`;
- `oldWave(n) → leftOneWave(0)`, `twoWaveRoot(n1=n+2, r)`, `cphaseD0Odd(r=1,m)`, `c0D1Odd(n+3,m)`, or `cphaseD1(r=2)`;
- `leftOneWave(n) → leftOneWave(n+3)`, `oldWave(2)`, `zeroLeftEven(3)`, or `oddEvenPrefix(7)`;
- `zeroLeftEven`, `evenPrefix`, and `oddEvenPrefix` each lead to `cphaseD1(r=3)`;
- `twoWaveRoot` and `c0D1Odd` each lead to `oldWave(2)`;
- `cphaseD0Odd(r=3,m)` leads to `zeroLeftEven(m+3)` or `oddEvenPrefix(2m+7)`; `cphaseD0Odd(r=1,m)` leads to an `oldWave`;
- `cphaseD1(r=3)` leads to `cphaseD1(r=3 or 4)`, `leftOneWave(0)`, `oldWave(0 or 244)`, or `cphaseD0Odd(r=3)`; the other observed C-phase edges are (2\to3) and (4\to3).

The observed graph is strongly connected: every family reaches `oldWave` or `cphaseD1`, and those families reach the rest. This is a promising candidate for a finite macro-state invariant. It is **not** yet a closure theorem: the edge relations were checked only on the bounded blank-root orbit, and the return theorems' local hypotheses do not by themselves constrain every untouched part of the tape.

## B/0 shield audit

A separate 10M replay maintained an incremental index of every tape occurrence of the forbidden word `1100` and queried it at each B/0 checkpoint. It found **0 unsafe B/0 checkpoints among 22,984**. This checks the full left-of-head region, not merely a fixed-width neighborhood.

The exclusion is not a primitive-step invariant. The replay includes an F/1 configuration with immediate left triple `110`; its F/1 write can create a temporary `1100` ending at the old head. The relevant wave-return theorem must restore the suffix before the next B/0 checkpoint. The useful invariant is therefore checkpoint-level, exactly as in `Root119GlobalShield.lean`, rather than a ban on `1100` at every intermediate configuration.

## Research consequence and limits

The 10M replay no longer exhibits a gap in its B/0 first-return classification. In particular, the eight two-wave-root intervals that previously followed an unclassified prefix are now preceded by a fully classified sequence in the bounded replay. The updated script therefore expects all eight to have `chainKnown` rather than `chainUnknown`.

This is **not** yet a formal Lean proof that all 22,984 B/0 configurations are reached from blank:
- the new `zeroLeftEvenRun_exact` proof patch is not compile-verified;
- the updated census script is not yet run in Node/CI;
- the finite replay's macro predicates and parameter checks are computational evidence, not a Lean certificate of the entire 10M-step history;
- even a formally certified 10M prefix would not establish an all-time invariant or decide the blank-root machine.

The next useful step is to compile the zero-left macro, run the extended census in the existing manual-only workflow, then construct a compact source-level certificate for the finite macro chain. The larger mathematical obligation remains an inductive all-time reachable B/0 language excluding the stopping gate, or a genuine reached gate witness. No BB(6) value or universal six-state upper bound follows from this audit.
