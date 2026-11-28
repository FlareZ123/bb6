# Raw34: tape-guarded entries and a genuine two-sided unbounded sweep

**Status (28 November 2026):** Original-source Lean theorems have been committed;
their Lean 4.36.0-rc2 CI checks are *pending*. The equations and arithmetic
below are candidate results until the source-gate jobs succeed. No complete
Raw34 cover, BB(6) upper bound, or exact Busy Beaver value is asserted.

## 1. Guarded E0 and F0, with unknown instructions allowed to HALT

See [Raw34GuardedE.lean](Raw34GuardedE.lean) and
[Raw34GuardedF.lean](Raw34GuardedF.lean). Both start with authentic Raw34
instructions `A0=1RB, B0=1RC, C0=0RD, D0=1LC`.

For E, set `B1 ∈ {0LE,1LE}`. For F use `B1 ∈ {0LF,1LF}`.
Every one of `A1,C1,D1,E1` (or `A1,C1,D1,F1`, respectively) may
be any of **13** ordinary moves: the 12 combinations of write bit,
direction, and successor among `A,C,D`, or the one protected jump
`1RB`. All three other instructions of E's family
`E0,F0,F1` (respectively F's `F0,E0,E1`) are free, including HALT.

The invariant over a complete original blank-tape configuration is

```text
control A, C or D
OR (control B AND tape[head - 1] = 1)
OR (control E AND tape[head] = 1).
```

Its F counterpart changes only E to F. Every transition into B writes a
1 at the predecessor cell by moving right, so B is *marked behind*. A
left-moving B1 transition arrives in E/F on that marked predecessor cell:
hence the E0/F0 instruction is never queried. The other permitted
instructions preserve the invariant. Induction proves arbitrarily many
live steps uniformly for **every total completion** of these partial
tables. This is tape-sensitive and not implied by an ordinary all-symbol
closed-control graph, because E0/F0 may itself be HALT.

Each guarded family contains exactly `2*13^4*25^3 = 892,531,250`
physical completions. The special E0-HALT subfamily has
`2*13^4*25^2 = 35,701,250` tables. The finite exact arithmetic
[Count portfolio](count_portfolio.mjs) uses the 3,087 already source
accepted Raw34 patterns and Agent40's nine prior closed-graph families.
It predicts **14,395,550 additional** E-guarded completions beyond
that specific prior portfolio, including **3,103,750 with E0=HALT**.
The F family is disjoint from E by B1's target and may contribute
further distinct tables. Do not interpret this as the entire
Raw34 complement classified; other proof mechanisms also exist.

## 2. Zero-predecessor entry guards from D and initial A

The same *marked predecessor* principle has two more applications,
each in both E-exit and F-exit forms. Unlike finite simulations,
their candidate proofs preserve an invariant on **every** original step.

**D guard:** [Raw34ZeroGuardedE.lean](Raw34ZeroGuardedE.lean) and
[Raw34ZeroGuardedF.lean](Raw34ZeroGuardedF.lean). Root instruction
`C0=0RD` writes a zero left of state D's new head; all other D
entrants are restricted to that same 0RD action. The D1 branch moves
left to E/F, guaranteed to scan zero. A1,B1,C1,E0/F0 may choose
the 12 ordinary moves into A/B/C or 0RD, preserving the invariant

```text
state A, B or C
OR (state D AND tape[head - 1] = 0)
OR (state E/F AND tape[head] = 0).
```

E1/F1 is unreachable, including when assigned HALT. Each family
contains `2*13^4*25^3=892,531,250` physical completions. Exact
arithmetic predicts **52,905,450 E** and **145,517,450 F** additional
tables beyond the accepted 3,087 Raw34 cylinders and Agent40's nine
graph families. The E1-HALT E subfamily alone adds 12,041,250
completions by this comparison. Source Lean CI is pending.

**Initial A guard:** [Raw34InitialZeroGuardE.lean](Raw34InitialZeroGuardE.lean)
and [Raw34InitialZeroGuardF.lean](Raw34InitialZeroGuardF.lean).
Blank tape already gives initial A a zero immediately left of its
head; every later A entry is forced to be 0RA, preserving that
marker. A1 moves left into E/F, and B1,C1,D1,E0/F0 choose from
the 12 ordinary moves into B/C/D or protected 0RA. E1/F1
cannot be queried even if HALT. The candidate incremental
arithmetic predicts **3,981,250 E** and **3,981,250 F** new
tables, including 796,250 E1/F1-HALT completions per target.

All eight family domains (these six guarded families and both
two-sweep variants below) are pairwise disjoint in their A1, B1 or
D1 instructions. Their contributions *outside the same prior
portfolio* may therefore be added exactly. The reusable BigInt
finite-domain proof audit is [count_portfolio.mjs](count_portfolio.mjs).
These local calculations do not establish any BB(6) global bound.

## 3. Alternating two-sweep counter with cost 28n+44

See [Raw34AlternatingTwoSweep.lean](Raw34AlternatingTwoSweep.lean) and
[Raw34AlternatingTwoSweepF.lean](Raw34AlternatingTwoSweepF.lean).
Source partial table:

```text
1RB0LB_1RC1RE_0RD0LA_1LC0LD_0RA---_------
```

E1, F0, F1 are truly unassigned. This machine's exact zipper
configuration `Z0` has a source-state B frontier family

```text
family(n) = (B, left=[], right=001(01)^(2n)0)
```

with an *explicit final zero* in the list representation. The candidate
source-level proof is a finite computation to `family(0)` in nine
ordinary moves, then five local certified transfers:

1. an 11-step preparation `001R → 0001R`;
2. a 6-step rightward pump `B/1 : 01 → 01` repeated `2n+1` times;
3. a four-step right-frontier turn;
4. a seven-step C/D/A turn into leftward sweeping state B;
5. an eight-step leftward pump `B/0 : 01 → 01` repeated `2n+2` times.

Both single-block lemmas quantify over *arbitrary untouched tape tails*,
so their two list-repetition inductions prove

```text
run0 p (28*n+44) (family n) = some (family (n+1)).
```

Hence the source partial machine never queries E1,F0,F1, and every
total completion (even those with HALT assigned there) is nonhalting.
In the original absolute tape coordinates, the same checkpoint times
are `14*n^2+30*n+9`. The 3 free entries mean `25^3=15,625`
physical completions in this single cylinder; exact overlap arithmetic
against the previously certified Raw34+Agent40 portfolio predicts
3,125 previously unclassified by that portfolio.

## Why this matters / next action

This is a **complement** proof: it closes long-running trajectories of
original partial machine cylinders rather than increasing simulation
horizons. Connect each source-accepted NeverHalts leaf into the live
weighted-cover refinement. Use the exact union audit and fresh residual
frontier generator to quantify which Raw34 subtrees remain unresolved.

CI modes of `.github/workflows/agent50-raw47-lifted.yml`:
`raw34-guarded-e`, `raw34-guarded-f`, `raw34-zero-guarded`,
`raw34-initial-guarded`, `raw34-two-sweep`.
The corrected baseline exact-union mode `raw34-union-audit`
passed as GitHub Actions run 46108131428.
