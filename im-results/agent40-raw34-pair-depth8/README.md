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
- 4,274 explicit residual rows;
- 1/7/67/604 finite-halting leaves at depths 3/4/5/6;
- 17/101/1,002/10,155 short side-cycle leaves at depths 3/4/5/6;
- 25 additional extended side-cycles at depth six;
- 4,234 open depth-six residuals;
- 40 long depth-six residuals;
- 42 depth-six leaves closed immediately by the finite state set {A,B,C,D,F};
- exactly **two** long depth-five residuals.

The residual physical mass at that point is therefore

`(4234+40)*25^2 = 2,671,250` after the two depth-five growth leaves are consumed

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
2n^2+7n.  The easy-plan certificate type consumes both growth theorems as leaves, so
all depth-five residual mass is removed from the explicit residual set and only
the 4,274 depth-six residual cylinders remain.
The 42 newly closed depth-six leaves require no dynamical recurrence: both E
rows are free, while every A/B/C/D/F row is assigned an ordinary transition
whose next state remains in {A,B,C,D,F}, so `Raw34Plan.Cert.closed` applies
at entry zero.

The earlier 131,081-table deeper census has now been superseded by
`census_f0ld.cpp`, which exactly replays the corrected source-plan
semantics and the state-major physical choice order.  Starting from the
4,274 depth-six residual cylinders (2,671,250 physical completions), it finds:

- 78,968 short sidecycles, 4,234 halts, 20,605 next-query branches, and
  2,043 long traces at depth seven;
- 767 of those 2,043 long depth-seven branches are certified by the existing
  larger half-line window (entry <= 500, period <= 200, trace cap 1,000),
  leaving exactly 1,276 one-hole long cylinders;
- all 20,605 open depth-seven branches are exhausted at depth eight:
  455,952 short sidecycles, 20,605 halts, and 38,568 long complete machines;
- every one of those 38,568 long complete machines has a finite closed
  state set reachable from A, so it is a candidate for the existing
  `Cert.closed 0 ss` source theorem.

Consequently the first deeper cut leaves **56,900 = 40*625 + 1,276*25**
physical completions.  Exhausting the final holes gives a much smaller exact
candidate frontier: all 23,040 ordinary/ordinary completions of the 40
two-hole cylinders are closed-state nonhalters, and all 30,624 ordinary
completions of the 1,276 one-hole cylinders are closed-state nonhalters.
Three of the 1,276 HALT completions halt finitely.  Therefore the remaining
candidate frontier is exactly **3,233 complete machines = 1,960 + 1,273**.  These are only **1,313 exact partial search targets**:
40 two-hole cylinders contribute 49 HALT-bearing hard completions apiece,
while 1,273 one-hole cylinders contribute one hard HALT completion apiece.
This grouping is exact finite arithmetic and is now asserted per cylinder by
`census_f0ld.cpp`.
A direct simulator run additionally found no halt among these 3,233 through
one million ordinary moves; that simulation is exploratory evidence, not a
proof.

Thus 2,668,017 of the original 2,671,250 depth-six residual physical
completions already have finite certificate shapes or finite halts at the
candidate level.  This 56,900 figure remains intermediate until the corresponding
source bank is kernel checked; `generate_full8_covers.mjs` separately
source-generates complete row Covers for the large easy tranche, while
`generate_pair_depth6_plan.mjs --root-shards` removes the monolithic
kernel-check bottleneck for the exact pair-parent plan.
