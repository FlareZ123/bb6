# Raw34 D1=0LF, F0=0LA depth-seven/eight census

This directory continues the exact split-plan program for the literal Raw34
subparent

`1RB---_1RC---_0RD0LF_1LC---_---0LA_------`

(the physical table is represented by source codes
`[21,0,22,0,11,0,16,7,0,0,2,0]`).  The parent has `25^6 =
244,140,625` physical completions.

## Starting point

`../agent50-raw34-plan/generate_pair_depth6_plan.mjs` exhaustively follows
the genuine first-undefined transition through depth six.  Its source plan has
39,676 nodes and 12,356 explicit residual rows.  The residual physical mass is
8,892,500:

- 11,571 open depth-six cylinders, each with two free slots (mass 625);
- 732 long depth-six cylinders (mass 625);
- 52 long depth-five cylinders (mass 15,625);
- one long depth-four cylinder (mass 390,625).

The generator now also writes `residualRows.json` so this frontier can be
consumed without parsing generated Lean source.

## New depth-seven/eight census

`census.cpp` reads that exact residual-row file.  It only expands the 11,571
rows whose 100-step partial execution reaches another genuinely undefined
transition.  For every physical choice it replays the same transition semantics
and the same short side-cycle predicate used to propose the accepted
`fastSideCycleCheck_sound` witnesses elsewhere in the Raw34 program.

Depth seven contains 289,275 children:

- 198,646 side-cycle candidates;
- 11,571 finite-halting candidates;
- 62,061 children that reach one last undefined transition;
- 16,997 long-trace children.

Expanding exactly those 62,061 open children through the last free transition
gives 1,551,525 complete machines:

- 1,233,087 side-cycle candidates;
- 62,061 finite-halting candidates;
- 256,377 long complete machines.

Thus the short-checker candidates newly classify 6,550,573 physical
completions beyond the depth-six plan: 5,255,425 at depth seven and 1,295,148
at depth eight.  If every emitted candidate is independently source-checked,
the pair-parent residual would fall from 8,892,500 to **2,341,927** physical
completions, so 241,798,698 of the 244,140,625-table parent would be decided.

The remaining 2,341,927 tables split exactly as

`256,377 + 16,997*25 + 732*625 + 52*15,625 + 390,625`.

## Evidence status

This is an intermediate computational census, not yet an academic result and
not yet a parent `Cover`.  Candidate generation is untrusted by design.
Side-cycle and finite-halting candidates must be emitted in source shards and
checked by the original Lean theorems before their mass may be promoted into a
proof bank.  The important research reduction is that the difficult remainder
for this 244-million-table subparent is now an explicit 2,341,927-table target,
dominated by long traces rather than unknown first-query branching.

Local reproduction on 28 November 2026 compiled `census.cpp` with
`g++ -O3 -std=c++20` and completed the depth-seven/eight census in 5.25
seconds after generating `residualRows.json`.


## Better pair target: D1=0LF, F0=0LD

A complete rank of the 100 physical (D1,F0) pair roots using
`rank_pairs_depth6.cpp` identified

`1RB---_1RC---_0RD0LF_1LC---_------_0LD---`

as a substantially better unresolved pair parent than the original F0=0LA
pilot.  The exact extended source-plan generator now supports this parent
directly (`generate_pair_depth6_plan.mjs --f0 0LD`) and asserts the
following depth-six census:

- 16,976 total plan nodes;
- 4,276 explicit residual rows;
- 1/7/67/604 finite-halting leaves at depths 3/4/5/6;
- 17/101/1,002/10,155 short side-cycle leaves at depths 3/4/5/6;
- 25 additional extended side-cycles at depth six;
- 4,234 open depth-six residuals;
- 40 long depth-six residuals;
- 42 depth-six leaves closed immediately by the finite state set {A,B,C,D,F};
- exactly **two** long depth-five residuals.

The residual physical mass at that point is therefore

`(4234+40)*25^2 + 2*25^3 = 2,702,500`

out of the pair parent's 244,140,625 completions.  A dedicated workflow mode
`raw34-pair-easy-plan` kernel-checks the generated source `Cover`; the
numerical census is a generator assertion and should be paired with a
successful workflow run before being treated as source accepted.

The two depth-five residual cylinders are exactly

`1RB1LA_1RC1RB_0RD---_1LC0LF_------_0LD1LA`

and

`1RB0LF_1RC1RA_0RD---_1LC0LF_------_0LD1LA`.

Each has three arbitrary rows (C1,E0,E1), hence physical mass 15,625.
`../agent40-raw34-frontier/Raw34QuadraticPairGrowth.lean` gives parametric
sweep-pump proofs for both.  The first grows a contiguous block with checkpoint
time n(n+8); the second grows an alternating block with checkpoint time
2n^2+7n.  Once both theorems are source accepted, all depth-five residual mass
for this pair is closed and only the 4,274 depth-six residual cylinders remain.
The 42 newly closed depth-six leaves require no dynamical recurrence: both E
rows are free, while every A/B/C/D/F row is assigned an ordinary transition
whose next state remains in {A,B,C,D,F}, so `Raw34Plan.Cert.closed` applies
at entry zero.

A deeper candidate census using the same short side-cycle checker, then the
repository's larger half-line search window (entry <= 500, period <= 200,
trace cap 1,000), reduces the unresolved physical target further to 131,081.
That number is **candidate-level only** until those deeper candidates are
emitted as source theorems and kernel checked.  Its useful structural
breakdown is 82 long depth-six cylinders, 1,276 long depth-seven cylinders,
and 16,681 complete depth-eight long machines after the two depth-five
growth cylinders are separated.
