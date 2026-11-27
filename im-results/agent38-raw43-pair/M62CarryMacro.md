# Raw43 B1=0LE, E0=1LA, i62: an all-parameter F0 carry macro

**Status (27 November 2026): mathematical derivation in the literal partial six-state machine, and reproducible finite tests; original-source Lean proof and a closed blank-root invariant remain outstanding.** This is an intermediate result, not a decision of M62, a Raw43 parent Cover, or BB(6).

## Exact machine and claim

The partially specified literal table, with F1 undefined, is

```
1RB0LA_1RC0LE_0RD1RF_1LD0RB_1LA1RA_0RE---
```

Use a bi-infinite tape, one primitive transition per instruction, positive positions to the right, and let the initial state be F scanning the first zero of the trailing block of five zeros. For `N >= 1`, integers `r_1,...,r_N` must satisfy

- `r_1 >= 1` when `N=1`; when `N>=2`, `r_1 >= 2`;
- `r_i >= 2` for `2 <= i < N`;
- `r_N >= 1`.

Let `S = sum_i r_i`. The finite input interval from position `-(S+N+1)` through position `+4`, inclusive, is

```
00  1^r1 0 1^r2 0 ... 0 1^rN  00000
```

(the middle separators are single zeros). The two exterior infinite tails are **arbitrary**. After **exactly `S + 18 + 9*N` primitive transitions**, the machine returns to state F, positioned at offset **`2-S-N`** from the initial head, scanning **zero**. All exterior cells are unchanged. The entire original finite interval is then

```
11101  (0^(r1-2) 101) ... (0^(r(N-1)-2) 101) 0^(rN-1) 101
```

for `N>=2`; for `N=1` the output is `11101 0^(r1-1) 101`. In particular, **F1 is not queried during this macro**, regardless of the surrounding tape.

This is a mathematically explicit infinite family of valid original-machine sections, not an assertion that every blank-reached F0 configuration belongs to the family. A proof of that global closure, including the other forward-return macros, is still required to prove M62 nonhalting.

## Exact primitive-word derivation

Write state-read pairs as `A1`, `F0`, etc. Define fixed instruction words

```
P = F0 E0 A0 B1 E1 A0 B0 C0 D0 D0 D1 B1 E0     (13 transitions)
Q = A0 B0 C0 D0 D0 D1 B1 E0                    (8 transitions)
R = A0 B0 C1                                     (3 transitions)
```

The **complete** instruction-word trace is

```
P ; A1^(rN+2) ; Q ;
  A1^(r(N-1)+1) ; Q ; ... ; A1^(r1+1) ; Q ;
  A1 ; R
```

where for `N=1` this reduces to `P;A1^(r1+2);Q;A1;R`.

The proof needs only three primitive local identities, plus the trivial A1 sweep:

1. **P:** at F scanning the first of five zero cells `00000`, P changes those five cells to `11101` and ends at A scanning position +1, which now contains 1. Its head never moves outside positions 0..4.
2. **A1 sweep:** A1 writes 0 and moves left. A run of `k` consecutive ones is erased in `k` transitions, ending at A scanning the zero immediately to its left.
3. **Q:** at A scanning `0000` (head plus three following cells), Q changes them to `1101`, ending at A scanning the original head position, now containing 1. Its head remains within that four-cell interval. The last `k>=3` A1 steps in the immediately preceding sweep supply the three following zeros. Hence the necessary inequalities on the `r_i`.
4. **R:** when the last Q is at the second of the two original leading zero cells, one A1 step erases that cell and enters the first leading zero. R writes three consecutive ones, moves right three places, and returns to F scanning zero (the third cell following Q's starting point).

After P, the first A1 run comprises its two new ones (positions 1 and 0) and the final input `1^rN`: length `rN+2`. Each following A1 run comprises the newly written separator 1 and the next original run `1^ri`: length `ri+1`. The final A1 erases Q's newly written cell at the second leading zero. Therefore the trace is enabled for every parameter tuple in the stated domain. Summing word lengths gives

```
13 + (S + 2 + (N-1)) + 8*N + 1 + 3 = S + 18 + 9*N.
```

The A1 sweeps make a total of `S+N+2` left moves, starting at head `+1` and thus ending at `-(S+N+1)`; the final R shifts three cells right, yielding head offset `2-S-N`. Tracking the four-cell Q rewrites from right to left, followed by A1 erasures, produces exactly the stated output word. Every visited cell belongs to the displayed interval, so the exterior tails remain arbitrary and untouched. The terminal scanned symbol is zero.

The fragment is a **paper proof** of a parametric execution identity using the explicit literal transition table; it has **not** been submitted as an original-source Lean theorem. If formalizing, prove P, Q and R as `run0` zipper identities with arbitrary tails, then induct on `N` (or a list of run lengths) and on the unary A1 sweeps, with explicit positive costs.

## Reproduction / falsification

The independently written exact simulator in `M62CarryMacro.cjs` reconstructs the literal 12-row table, tests the full output and terminal state/head, and checks the predicted instruction-word factorization and the arbitrary exterior unchanged. Executing the committed test script validates all `r_i in {1,...,7}` for `N=1,...,4` (1,813 valid-domain tuples), plus 480 longer run lists (`N=1,...,12`), with **zero discrepancies across 2,293 tests**. The initial exhaustive range also has 987 out-of-domain tuples that were excluded rather than used to extend the theorem. The exact committed script was run successfully through a V8 JavaScript evaluator and printed its success report. These are software tests, not a Lean proof.

In the first million literal blank-tape transitions, the machine visits F0 more than 44,000 times and does not query missing F1. This is **finite evidence only**. Frequent other F0 first-return macro types are (steps, relative final head): (8,+6), (18,+6), (11,+5), (11,+7). Those other return shapes need to be composed with the backward carry family in a genuine blank-root invariant; a long replay does not close that obligation.
