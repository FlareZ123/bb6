# #429: authentic writer prefixes admit synthetic one-sided fatal continuations

**Original-source Lean-certified finite locality obstruction (9 November 2026), [successful CI 42544324043](https://github.com/FlareZ123/bb6/actions/runs/42544324043).** The machine is the genuine six-state table `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`. Its blank-origin nonhalting and BB(6) remain **open**. This finding concerns the information needed to infer the C/01 gate from writer configurations. It does not exhibit an authentic blank-origin C/01 event.

## Exact claim and reproducibility

The source table from [the original physical model](../agent1-429-physical-frontier/BB429PhysicalFrontier.lean) gives these two *true-blank* finite configurations:

| Primitive time | Real state and head | Eight left bits, near-to-far | Prepared source | Synthetic one-sided C/01 time |
| --- | --- | --- | --- | --- |
| 276 | D/0 at 16 | 0xFE | D/0 at 0 with left ones at -2 through -8 | 27 |
| 283 | F/1 at 9 | 0x57 | F/1 at 0 with left ones at -1,-2,-3,-5,-7 | 59 |

The prepared tapes are **synthetic, freely chosen**. Their eight nearest left bits and state/scan bit exactly match the authentic configurations. Each synthetic execution writes 1 at its writer boundary 0, remains at head position at most 0 for every instruction-start time through the fatal visit, and reaches C scanning 0 at head -1 with the right neighbor 0 marked 1. The original halting biconditional [Agent32](../agent32-429-raw-parent/README.md) establishes that C/01 is fatal for machine #429.

Each genuine configuration has a one at position relative -9. The corresponding prepared tape instead has zero at -9. The first differing read is at relative head -9 after 9 (D) or 13 (F) primitive instructions. Thus **the current writer row and its eight nearest left bits, even together with the one-sided-head condition, cannot alone rule out a fatal return**. A sound rooted proof needs additional distant-tape or history information.

Run `python writer_locality.py` to reproduce both 0-origin trajectories, the prepared fatal visit times, the one-sided head bound, and the first read divergence. The script uses the literal 11 nonhalting source rows, a sparse all-zero-elsewhere tape, and assertions for every reported quantity. The test is finite; the complete unbounded criterion is still unknown.

[Lean source](BB429WriterLocality.lean) states both finite original-source physical traces, one-sided head bounds, and the authentic 276/283-step writer observations. All six assertions were compiled against the repository's unchanged physical table and dependency chain in [manual CI 42544324043](https://github.com/FlareZ123/bb6/actions/runs/42544324043), commit `d1056189ffc3285985d5b9e24c5df865ace52abc`. Every corresponding `#print axioms` reports **no axioms** (fully kernel-reduced `by decide`), and the CI command rejects `sorryAx`. These are exact finite source-certified statements. The Python assertions independently reproduce the trajectories.

## Interpretation and remaining question

The existing [Agent18 last-writer theorem](../agent18-429-lastwriter/README.md) gives three exact possible write-one/left source rows (D/0, E/1, F/1) for any hypothetical blank-origin fatal event. It also supplies a synthetic E/1 fatal tape. The present D/0 and F/1 tapes extend this negative test to **all three writer types**, and the finite true-blank prefix comparison strengthens it for D and F by matching actually encountered eight-cell neighborhoods. Earlier [factor-closure failure](../agent6-429-regular-screen/README.md) concerns another local abstraction and does not imply any genuine fatal visit.

A useful next proof attempt should preserve the **ninth and more distant left-tape bits** or a true-blank return-history invariant, and test whether its constraints survive the authenticated Junc return grammars. Neither the match at eight bits nor the synthetic fatal suffix provides a full root decision. This dossier remains in `im-results/` because no new publishable Busy Beaver value or broad machine-class theorem is claimed.
