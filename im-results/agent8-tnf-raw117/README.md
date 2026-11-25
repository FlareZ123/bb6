# Six-hole raw117 and raw112 candidate classification

Raw117 is the six-hole sibling E1=1RD, parent `1RB---_1RC---_0RD---_1LD1RE_---1RD_------`. Raw112 differs only at E1=1LC. Both have exactly 25^6 = 244,140,625 compatible full tables.

| raw | splits | side cycles | last holes | open leaves | FAR candidates | symbolic candidates | late query | still open |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 117 | 7903 | 143850 | 32350 | 5570 | 5530 | 36 | 1 | 3 |
| 112 | 25004 | 446232 | 115572 | 13289 | 12896 | 0 | 0 | 393 |

These are **candidate counts**, not kernel-accepted source certificates. The raw117 finite search cutoff is 1000; a later query on leaf 2707 at ordinary time 1290 reaches its only hole F0. All fixed zero-writing rows fail to enter A, so its exact weighted score is 1291 (zero incoming delay). The earlier maximum 235 is superseded. Raw112 initial candidate maximum 980 is provisional.

The 36 symbolic candidates consist of 30 single-block sweep returns, four two-block returns, one extended six-sweep return (1747, entry 17, cost 116+96n), and one fixed 309-step return (3890, entry 124). The latter does not inspect the variable suffix. Both extra returns are candidate opaque-word computations, not formal theorems yet.

Remaining raw117 leaves:
- 397 `1RB1LF_1RC1LB_0RD0RE_1LD1RE_0LA1RD_---0LB`: nested sweeps, B fresh-left return grows four ones.
- 4215 `1RB1LE_1RC0RB_0RD---_1LD1RE_1LF1RD_1LA0LF`: alternating growth of unary prefix and zero gap.
- 4216 `1RB1LF_1RC0RB_0RD---_1LD1RE_1LF1RD_1LA0LF`: closely related to 4215.

## Reproduction

Run `python im-results/agent8-tnf-raw117/discover.py 117` or `112`. This uses the existing raw99 enumerator and six-hole FAR bank checker, pins the exact ordered open list by SHA256, rechecks the bank coverage and lists unresolved IDs. Banks are compact sets of actual successful witnesses, including newly discovered DFA mutations. Run `--sweeps` for raw117 to emit the 36 candidate Lean proof terms via the existing one/multi-block generators. No claim of full Lean source acceptance is made until all certificates compile and the canonical roster graft passes. The source C++ tools are reused rather than duplicated. No BB(6) upper bound follows yet.
