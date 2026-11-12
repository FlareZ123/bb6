# Counted TM63 reset drain

This is an intermediate proof module for the repeated decrement phase
(`Incs0`) used by the published TM63 `Rst0`, `Rst1`, and `Rst2` macros.
It is deliberately separate from Agent 46's `Rst1'` reset-core project.

## New arithmetic bridge

`CountedReset.lean` proves that the actual descending 2-adic valuations
of the counter values (2^b-1,2^b-2,ldots,1) are exactly
`CountPattern.carryPattern b`:

- `v2_add_pow` proves (v_2(2^b+k)=v_2(k)) for (0<k<2^b);
- `descV2_shift` gives the exact dyadic block decomposition;
- `descV2_binary` identifies the descending valuation word with the
  recursively defined carry pattern;
- `drainCost_binary_closed` derives
  (6cdot4^b+42cdot2^b-12b-48) from the actual per-decrement costs.

This closes a useful logical gap between a recursively generated carry
pattern and the valuations of the concrete counters encountered by the
reset loop. It is stronger than matching only the list length and total sum.

## Original-machine run composition

The module defines
`inc0Cost z c = 48 + 12*v2(z) + 12*c` and the corresponding recursive
`drainCost n c`. The theorem `countedIncs0` proves, in the original
`BB6Coverage.run` semantics, that any family of counted one-step
`Inc0` runs composes to the full `Incs0` drain:

`S0(l,len,n,c) -> S0(l,len,0,c+n)`.

For the all-ones counter, `countedIncs0_binary` specializes this to
`2^b-1 -> 0`, with exact cost `drainPattern b`. The only machine-specific
premise is the uniform single-decrement theorem; the repeated-run
composition, endpoint arithmetic, and exact drain cost are proved here.

## Reset-stage interface

`proposedIncrementCost_decomp` proves the candidate Rst0/Rst1/Rst2 cost
from Agent 24's `CostRecurrence.lean` splits exactly into:

- a candidate prefix cost
  (48+12(a+v_2(n))+15+4m+3b), and
- the proved all-ones `Incs0` drain `drainCost (2^b-1) 0`.

`countedRst012_of_prefix` is the corresponding original-run composition
theorem: once a counted prefix reaches the S0 intermediate with second
counter (2^b-1) and right counter zero, the exact candidate total cost
reaches the reset endpoint with second counter zero and right counter
(2^b-1).

The prefix theorem and the uniform single-step `Inc0` theorem remain
explicit premises. This module does not claim that either has already
been established as a source-level run theorem. Agent 24 is lifting the
uniform local carry theorem into the original infinite-tape semantics;
Agent 8's contribution here is the exact reset-drain composition and
valuation identity.

## Dependencies

- `im-results/agent8-s1-encoder/S1Encoder.lean` for the source S0
  configuration `s0Config`;
- `im-results/agent24-champion-time/CostRecurrence.lean` for `v2`
  and the proposed Rst0/Rst1/Rst2 cost;
- `im-results/agent24-champion-time/CountPattern.lean` for
  `carryPattern`, `charge`, and `drainPattern_closed`;
- `im-results/agent48-champion-root/ChampionRootBridge.lean` for the
  original TM63 transition table and configuration semantics.
