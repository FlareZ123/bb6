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
