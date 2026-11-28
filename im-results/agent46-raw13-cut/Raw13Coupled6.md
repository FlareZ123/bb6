# Raw13 six-hole exact-threshold composition

This note records the current integration state for the Raw13 six-hole prefix

```
1RB1LD1RC---1LA1RE---0LA------------
```

represented by `BB6.Agent46Raw13CoupledParent.p3`.  It is intermediate
research documentation; the parent theorem is promoted only after its composed
Lean closure is source-accepted.

## Target theorem

The parent has six free transition rows, hence exactly

```
25^6 = 244140625
```

compatible concrete six-state/two-symbol completions.

The candidate exact weighted threshold is

```
B = 44423003584937617011264491061.
```

`Raw13Coupled6.lean` assembles the theorem

```
(∀ m, compatible parent m → WeightedBound N m) ↔ B ≤ N
```

conditional on the already used `NeverHalts published` hypothesis.
`Raw13Coupled6Source.lean` transports the pinned Cryptids nonhalting theorem
to discharge that hypothesis and states the unconditional version.

The lower bound is the exact, kernel-checked E1=1RA witness with halting index

```
44423003584937617011264491060
```

and zero first-one delay, so its weighted score is exactly `B`.

## E1 split

The first query of E1=(4,true) occurs after 8 steps.  The 24 nonhalting
assignments decompose as follows.

- E1=0RA is the direct exact cycle `cycle 0 9 true (-1)`.
- E1=1LC is the direct exact cycle `cycle 7 2 true 1`.
- E1=0RD is precisely the already composed five-hole parent
  `Raw13Coupled5`, bounded by 62123.
- E1=1RA has the exact bound `B`; its source-accepted sibling audit is
  workflow run 46103800697.
- E1=1LB is bounded by 2651340.
- E1=1LD and E1=1RD are bounded by 2651346.
- Every remaining generated sibling is bounded by 62123.

Thus no sibling other than E1=1RA can attain the parent threshold.

## Six-hole sibling audit state

Historical successful full sibling audits that remain useful proof artifacts:

| E1 branch(es) | workflow run |
| --- | ---: |
| 1RA | 46103800697 |
| 0RB, 1LA | 46037817669 |
| 0LE | 45976598144 |
| 0LB | 45975985504 |
| 1LE | 45975992299 |
| 1RD | 45975905856 |
| 1LB | 45974286731 |
| 0LF | 45958597960 |

Historical failures for 1LD and 1LF ended with runner shutdown signal 143,
rather than a Lean or mathematical failure.

The missing branches are being re-audited from the immutable Agent 46 claim
source.  Paired runs are used where possible:

| branches | workflow run |
| --- | ---: |
| 0LA, 0LB | 46140763426 |
| 1LB, 1LD | 46140776944 |
| 0LC, 0LD | 46140948605 |
| 0RB, 0RC | 46140956423 |
| 0RE, 0RF | 46140960782 |
| 1LF, 1RB | 46140968655 |
| 1RC, 1RE | 46140972765 |
| 1RF | 46140976373 |

The generated 1RA sibling has 49 unresolved search leaves before proof
attachment: 42 are covered by stored certificate banks and the remaining
seven are the four phased-counter instances, mirrored counter, unary recursion,
and the giant hierarchical halting leaf.  The generator accounts for all 49.

## Composition and source audit

`.github/workflows/agent46-raw13-coupled6-parent.yml` merges independently
accepted child proof artifacts, rejects byte-incompatible duplicate Lean
sources, compiles `Raw13Coupled6.lean`, rejects `sorryAx` and
`native_decide`, and preserves a composed proof artifact.

`.github/workflows/agent46-raw13-coupled6-source.yml` then checks the parent
against the unchanged pinned Cryptids theorem at revision
`3647718b5df22e1a61462dec0376bd204526285a` and proves the unconditional
exact-threshold statement.

Until those two final composition steps succeed, the six-hole theorem source is
an assembled candidate backed by accepted child results, not yet a
source-accepted parent theorem.
