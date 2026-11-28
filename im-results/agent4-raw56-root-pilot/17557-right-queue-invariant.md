# Raw56 leaf 17557: right-run queue safety

**Status:** Lean formalization in `Raw56LE17557RightQueue.lean`; CI run 46169872594 is the current source check. This is an intermediate lemma, not a complete nonhalting proof.

## Why this invariant is needed

The accepted source triads in `im-results/agent1-raw56/le/Raw56LE17557LocalSweeps.lean` have right-side preconditions that are easy to lose in a purely event-word argument:

- A-normal reads three consecutive one-runs, with one zero between the first two and at least two zeros after the third.
- A-carry has the same right-side shape, but its middle one-run has length exactly five.
- B reads two consecutive one-runs, with one zero between them and at least two zeros after the second.

The abstract event substitution and terminal-tag scan do not, by themselves, prove that these finite zero gaps remain large enough in the physical orbit.

## Queue representation

Use `Final(a)` for a final finite one-run of length `a`, followed by the infinite blank ray. Use `More(a,g,Q)` for a one-run of length `a`, followed by a finite zero-gap of length `g`, followed by queue `Q`.

The exact right-run effects extracted from the accepted local sweeps are:

- A-normal: `More(a,1,More(b,1,Final(c)))` becomes `More(2,1,Final(c+5))`; if the third run is nonfinal, its following gap `g` becomes `g-2` and its tail is retained.
- A-carry: the same rewrite, except the first output run is `a+d+4`, where `d` is the left one-run consumed by the carry.
- B: `More(a,1,Final(b))` becomes `More(2,1,More(5,a-1,Final(b+3))`; for a nonfinal second run, retain the old tail after inserting the run `b+3` and shortening its gap by two.

These are queue-level right projections of the source triad rewrites, not a replacement for their `run0` theorems.

## Inductive invariant

The formal predicate `Good` in `Raw56LE17557RightQueue.lean` states:

1. The first run is (2) or (6pmod 8).
2. The first finite gap is exactly (1).
3. If there are exactly two runs, the next event is a terminal B triad.
4. With at least three runs, the second run has length at least (5), and the gap after it is either exactly (1) or is at least (5) and (1) or (5pmod 8).
5. Every gap after the third run is (3) or (7pmod 8), and all those runs are positive.

The closure proof is short and local:

- A-normal/A-carry consume a third-run gap (gequiv3,7pmod8), so (g-2equiv1,5pmod8). It is either (1), or at least (5); all later gaps are unchanged.
- B consumes a second-run gap (gge5), (gequiv1,5pmod8), so (g-2ge3) and (g-2equiv3,7pmod8). Its newly inserted gap is (a-1), which is (1) or at least (5), in residue (1) or (5pmod8), because (aequiv2,6pmod8).
- A-carry preserves the first-run residue when (dequiv0pmod4).

The initial C₂ right queue is `More(2,1,More(5,1,Final(7)))`. Thus, assuming every carry's left one-run is divisible by four, every finite prefix of the right-run transducer exists and satisfies the source triad guards. The Lean theorem is `every_finite_prefix`.

## Remaining source integration

The one external hypothesis is (dequiv0pmod4) at every A-carry. The source A-normal sweep creates a left one-run of length (a+2), where (a) is the first right-run length; the queue invariant gives (aequiv2pmod4), hence (a+2equiv0pmod4). B leaves that older left one-run in place, and A-carry consumes it. This should be packaged as a small auxiliary one-run stack and paired with Agent 1's accepted `ActionGrammar` / `FrameMachine` zero-run closure.

The remaining major task is to compose the source `run0` triad sweeps with that left-frame execution, including the finite-list blank-padding relation. Until that composition is proved, this queue theorem is not a proof that the actual blank orbit follows the transducer, and it is not a BB(6) result.
