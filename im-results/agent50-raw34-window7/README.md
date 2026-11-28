# Agent 50: seven-cell physical Raw34 invariant bank

**Status: candidate mathematical theorem and 128 certificate bank.** The
original-source Lean 4.36.0-rc2 source-closure and standard-axiom gate is
queued via manual workflow `raw34-window7-domain-shards`. Do not
promote to `results/` or report as accepted proof until the source run
passes. This is a *local* Raw34 research increment and does **not**
determine BB(6).

## Genuine original-tape invariant (not a simulation cutoff)

`Window7General.lean` defines a predicate `P(q,L3,L2,L1,c,R1,R2,R3)`
over the seven actual tape cells centered at the head, so a blank-tape
initial state has seven false bits. An ordinary instruction must return
to `P` after moving either left or right, for **both** possible symbols
on the newly entering tape cell at distance four. An instruction with no
supported source observation can be absolutely anything, including
physical HALT. The source theorem

`BB6.Agent50Window7.never_of_permitted7`

states that **every total original six-state machine** whose twelve
physical transitions respect these local action domains diverges from
the authentic all-blank infinite tape. The proof maps the seven-cell
predicate to the established nine-cell window source invariant and
uses `BB429WindowLeaf.partial_finite_window_never` on the actual
original machine. There is no bounded tape or bounded time premise.

The literal child in `Window7Witness.lean`

```text
1RB0LB_1RC1LE_0RD1RC_1LC1LA_---0RA_------
```

has **75** abstractly reachable seven-cell windows and E0,F0,F1
unrestricted. The source `never` and `cover` theorems express
nonhalting for every 25³ physical completion, even a true HALT
instruction in one of the unvisited slots.

## Deterministic discovery and 25-action exact counting

`search_and_count.mjs` reconstructs `mask-bank-128.json` using
xorshift32 seed **8112019**, exactly **100,000** source-compatible
five-free-action trials, and both possible incoming boundary bits in
the seven-cell BFS. There are 2,159 closed samples that abstractly
read E1, giving 1,504 distinct Cartesian action domains, of which
319 have strictly positive individual marginal outside the older
three-thousand-cylinder/nine-graph/**256 five-cell domain** portfolio.
The 128 highest individually ranked candidate domains are retained.

Each of the eight `Window7DomainShard[0..7].lean` modules contains
16 literal seven-cell masks and their exact eight 25-bit physical
action-domain masks. `Window7BankDomainsCore.lean` defines an
independently kernel-reducible finite checker of every permitted
physical transition and all four source root instructions, including
the blank start. All source proofs explicitly check standard axioms,
no native evaluation or admitted proof.

An independent 25-ary ordered decision-diagram count uses physical
Root34 slots D1,C1,B1,A1,E0,E1,F0,F1 and bit 0 as **HALT**:

| Exact finite union against the specified older bank | Physical tables |
| --- | ---: |
| 3,087 source cylinders + nine closed-control masks | 123,226,284,000 |
| Plus 128 radius-two and 128 E/F-conjugate radius-two domains | 123,355,899,793 |
| Plus 128 seven-cell domains | **123,371,506,468** |
| Marginal seven-cell over the preceding 256 domains | **15,606,675** |
| Total Root34 table space | 152,587,890,625 |

These increments are **not relative to the latest Agent 40/23 source
accepted F/E halting, depth-six, sidecycle, growth and ray banks**. The
difference against that broader portfolio is an independent open
computation, and is checked using optional `--include-window7-mask-bank`
together with `--include-window5-mask-bank` in the existing
`rank_live_nonD1RD.mjs` and CI `raw34-window5-fullunion`.

## Implications and limitations

The mathematical method is a reusable original-infinite-tape
transducer-invariant family covering machine completions rather than
enumerating finite step cutoffs. Its ability to classify additional
Root34 candidates suggests richer seven-cell locality detects
behavior missed by all 256 five-cell domains. But this is a
**sufficient condition**, not a complete nonhalting decision method.
There remain many unclassified physical machines and the 39
conditional global BB(6) maximality obligations. Proper next work
is proof-source CI acceptance, then exact subtraction from the latest
accepted source union, and use in an explicit complementary Root34
proof tree.
