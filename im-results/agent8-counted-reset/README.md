# Counted TM63 reset drain and reset-prefix interfaces

This directory contains intermediate source-machine proofs for the repeated decrement phase (`Incs0`) and the Rst0/Rst1/Rst2 pre-drain prefix. These are not yet a complete universal reset theorem and do not establish the exact BB(6) score.

## Proved arithmetic and run-composition layer

`CountedReset.lean` proves that the actual descending 2-adic valuations of
`2^b-1, 2^b-2, ..., 1` are exactly `CountPattern.carryPattern b`:

- `v2_add_pow` proves (v_2(2^b+k)=v_2(k)) for (0<k<2^b);
- `descV2_shift` gives the exact dyadic block decomposition;
- `descV2_binary` identifies the descending valuation word with the recursively defined carry pattern;
- `drainCost_binary_closed` derives the closed drain cost from the actual per-decrement costs.

The module defines `inc0Cost z c = 48 + 12*v2(z) + 12*c` and the corresponding recursive `drainCost n c`. The theorem `countedIncs0` proves in the original `BB6Coverage.run` semantics that any family of counted one-step `Inc0` runs composes to the full `Incs0` drain:
`S0(l,len,n,c) -> S0(l,len,0,c+n)`.
For the all-ones counter, `countedIncs0_binary` specializes this to `2^b-1 -> 0`, with exact cost `drainPattern b`.

The machine-specific uniform single-decrement theorem remains an explicit premise. The repeated-run composition, endpoint arithmetic, and exact all-ones drain cost are proved; the universal source-level `Inc0` theorem is not.

## Reset-stage interface

`proposedIncrementCost_decomp` splits the candidate Rst0/Rst1/Rst2 cost into:

- a candidate prefix cost `48+12(a+v₂(n))+15+4m+3b`;
- the proved all-ones `Incs0` drain `drainCost (2^b-1) 0`.

`countedRst012_of_prefix` is the original-run composition theorem: once a counted prefix reaches the S0 intermediate with second counter `2^b-1` and right counter zero, the exact candidate total cost reaches the reset endpoint with second counter zero and right counter `2^b-1`.

The prefix theorem and uniform single-step `Inc0` theorem remain explicit premises. This module does not claim either has been established as a source-level run theorem.

## Finite marker-specific reset bases

`CountedResetBase.lean` records the exact finite source traces for the three marker cases with `a=b=0`:

| Marker m | Steps | Final state/head | Ordered marked cells |
|---:|---:|---|---|
| 0 | 63 | 3 / 5 | `[7,8,9,12,13,14,5,4,3,2,1,-1,-4,-5,-6,-7]` |
| 1 | 67 | 3 / 5 | `[7,8,9,12,13,14,5,4,3,2,1,0,-2,-5,-6,-7,-8]` |
| 2 | 71 | 3 / 5 | `[7,8,9,12,13,14,5,4,3,2,1,0,-1,-3,-6,-7,-8]` |

**Ordering is semantically significant.** `FConfig` uses a list and its equality is list equality, not set equality. Sorting the marked cells preserves the represented tape but makes the `fRun` endpoint equality false. The current output frames preserve the exact insertion/filter order of `fMove`.

`reset_base_check.js` independently replays the published TM63 table with the same ordered-list update rule and checks all three endpoints. This is reproducible computational evidence, not a proof. `resetBase_exact` is intended to certify the same traces by `decide`; the current fixes to its output order, `v2` qualification, and finite-head helper are committed but await the manual Lean audit.

The finite-base support changes are:
- use `BB6ChampionArithmetic.v2` explicitly in `resetBase_cost_eq`;
- use `even_finite_heads` from `CountedOneZeroUnary` in `resetBase_heads`;
- compile `CountedOddUnary` and `CountedOneZeroUnary` before `CountedResetBase` in the manual champion-root workflow;
- capture the reset-base compilation output and reject `sorryAx` with a dedicated CI gate.

These are source and workflow repairs, not a verified result yet: the manual-only champion-root workflow has not been dispatched after these commits.

These bases cover only `a=b=0`. They do not prove the universal prefix with arbitrary `a,b,v₂(n)`.

## Reset-prefix target

The intended source endpoint is

```text
S1(L,n,m,a,0,b,h)
  -->[resetPrefixCost m n a b]
S1(L,n-1,(m+2)%3,a+b+delta(m),2^b-1,0,h+5+3*b)
```

where `delta(0)=1` and `delta(1)=delta(2)=2`. In S0 notation the target is

```lean
s0Config (markerWord ((m+2)%3) ++ d0 ++ binDec L (n-1) ++ lh)
  (a+b+delta(m)) (2^b-1) (h+5+3*b)
```
The head displacement is **`5+3*b`**, not zero.

A direct simulator using the source TM63 table matched the full pre-drain endpoint (state, complete tape, and head displacement) in 684 finite parameter cases with `L<=5`, `n<=5` within the length bound, `m∈{0,1,2}`, `a<=3`, and `b<=2`. The observed head shift was exactly `5+3*b` in every case. This is computational evidence only, not a universal proof.

## TM63 q4 suffix frame

`Q4Suffix.lean` isolates the q4/head-0 suffix. It provides the intended `39+3*b`-step decomposition:

- fixed 10-move entry from state 4/head 0 to state 1/head 10;
- exact `3*b`-move scan of `b` additional three-one blocks in state sequence 1 → 5 → 3 → 1;
- fixed 29-move tail framed over the local read window `[-4,4]`, with arbitrary exterior tape.

The theorem `q4_suffix_frame` returns the output as a composition of `frameAt` and the counted block-scan transformation. The left exterior is unrestricted; five blank cells beyond the right unary run suffice for this run theorem. The list identity `q4SuffixTargetLeft` gives the expected canonical left word
`d0pow b ++ d1pow 2 ++ (q4LeftFacing L n a).drop 1`.

The source q4 prefix theorem is in `im-results/agent6-q4-prefix/CountedQ4Prefix.lean`. Its original finite-right-shape interface passed the q4-prefix CI gate in run `43334058991`. Agent 24 has strengthened the theorem to export its already-proved full right-facing stream; that signature change is not yet CI-verified. `im-results/agent24-champion-time/Q4RightEndpoint.lean` uses the stream to prove the suffix's complete right-facing endpoint, including the infinite blank ray. A coordinate split for the remaining left-facing endpoint is recorded in Agent 24's communication to Agent 8. Neither endpoint helper has been compiled in the current source revision.

The latest overall champion-root run `43340804651` failed, and the available job-step summary does not identify the failing Lean declaration. The manual audit now compiles the q4 modules before the independent reset-base module and compiles `CountedOneZeroUnary` before `CountedResetBase`; rerun it to check the current revisions. Do not treat any uncompiled helper as a verified theorem.

## Dependencies and ownership

- `CountedSweep.lean`, `CountedOddBase.lean`, and `S1Encoder.lean` provide the source encodings and counted operations.
- `CostRecurrence.lean` provides `v2` and the candidate reset cost.
- `CountPattern.lean` provides the carry pattern and closed drain arithmetic.
- `ChampionRootBridge.lean` provides the original TM63 table and configuration semantics.
- `CountedOneZeroUnary.lean` provides `even_finite_heads`.

The current ownership split is: Agent 8 develops the S1-to-S0 pre-drain prefix and q4 suffix; Agent 24 develops the generic arbitrary-valuation `Inc0` theorem and q4 endpoint bridge; Agent 42 owns the downstream terminal/score adapter. The main mathematical gap remains a source-certified universal reset prefix and the uniform single-decrement theorem.
