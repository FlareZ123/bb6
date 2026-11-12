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


## Reset-prefix target (current proof gap)

The source macro's first, pre-drain phase must be proved separately from the
already formalized `Incs0` drain. The exact intended source endpoint is

```
S1(L,n,m,a,0,b,h)
  -->[resetPrefixCost m n a b]
S1(L,n-1,(m+2)%3,a+b+delta(m),2^b-1,0,h+5+3*b),
```

where `delta(0)=1` and `delta(1)=delta(2)=2`. In S0 notation, the target is
`s0Config (markerWord ((m+2)%3) ++ d0 ++ binDec L (n-1) ++ lh)
  (a+b+delta(m)) (2^b-1) (h+5+3*b)`.
The head displacement is **`5+3*b`**, not zero. This is required when
feeding the endpoint into `countedRst012_of_prefix` and the downstream
terminal bridge.

The arithmetic decomposition is exact:

```
resetPrefixCost m n a b
  = inc0Cost n a + 15 + 4*m + 3*b.
```

A direct simulator using the source TM63 transition table matched the full
pre-drain endpoint (state, complete tape, and head displacement) in 684
finite parameter cases with `L<=5`, `n<=5` within the length bound,
`m in {0,1,2}`, `a<=3`, and `b<=2`. The observed head shift was exactly
`5+3*b` in every case. This is **computational evidence only**; it is not
a universal proof and must not be cited as one.

Ownership split: Agent 8 is taking this S1-to-S0 pre-drain prefix; Agent 24
retains the generic arbitrary-valuation `Inc0` theorem; Agent 42 owns the
downstream terminal/score adapter. The prefix remains the missing source-level
lemma. Do not conflate it with the already-proved all-ones drain.

## TM63 q4 suffix frame (new intermediate proof)

`Q4Suffix.lean` isolates the q4/head-0 suffix from Agent 24's
`LCIncQ4Cut.md`. It provides original-machine run theorems for:

- the fixed 10-move entry from state 4/head 0 to state 1/head 10;
- the exact (3b)-move scan of (b) additional three-one blocks in
  state sequence 1 → 5 → 3 → 1;
- the fixed 29-move tail, framed over the local read window ([-4,4])
  with arbitrary tape exterior.

The composition theorem `q4_suffix_frame` establishes the exact
(39+3b)-step run from a state-4 q4 cut, assuming its right-half shape.
It returns the resulting tape as a composition of `frameAt` and the
counted block-scan transformation. The left exterior is unrestricted.

This is **intermediate formalization**, not yet a completed canonical
`s1Config` endpoint theorem: the adapter identifying the framed output
with the target `s1Config` (and the upstream S1-to-q4 prefix theorem)
remain to be proved. The new module is included in the manual
`agent48-champion-root` Lean workflow, but no CI compilation has yet
been run for this addition. Do not cite the draft as a verified theorem
until that workflow compiles it and its axiom audit passes.
