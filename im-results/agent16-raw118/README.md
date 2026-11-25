# Raw118: candidate partition and long first-hole obstruction

Parent: `1RB---_1RC---_0RD---_1LD1RE_---0LE_------` (six holes, raw frontier index 118). Status: **partial discovery; no certified parent closure**.

Using Agent2's raw99 enumerator (1000 steps; translated-cycle window 256), the candidate tree partitions 25^6=244,140,625 physical completions: 227,709,700 cycle, 14,492,552 halt, 906,048 last-slot ordinary, 1,032,325 open. Tree census: 7,424 splits, 126,916 cycles, 37,752 last, 6,085 open. Initial maximum weighted halt score 992.

The shared seeded FAR search with canonical DFA size <=4 and bank union from raw112, raw115, raw114 produces 4,974 candidates (mass 972,750). Replay of the remaining leaves through one million steps finds 67 delayed last-hole candidates (mass 1,675). Sparse n-gram fixed-point search (widths 1–16, cap 200,000 states per attempt) finds 679 more (mass 25,975). Remaining: 365 leaves, mass 31,925, with 352 one-hole, 12 two-hole, one three-hole. These are untrusted candidate classifications pending original-source certificate acceptance.

## Important large halter
Open index 439 (zero-based, stable enumeration): `1RB1LE_1RC---_0RD1RA_1LD1RE_0LF0LE_1RF0RC`. Two simulations find first undefined row B1 after 756,495 ordinary transitions. Filling B1 with halt gives score 756,496; no nonzero incoming blank delay is possible because no read-zero transition writes zero and leads to A. A Lean 4.36.0-rc2 evaluation using copied zipper semantics returns the same B1 query. The direct kernel computation timed out, but the packed sweep certificate below kernel-checks the query against copied zipper definitions. Original-source CI run [45575655393](https://github.com/FlareZ123/bb6/actions/runs/45575655393) accepted both the trace and weighted last-hole certificate. Thus the proposed bound must be at least 756496, not 7014.

A locally kernel-checked packed zipper refinement and arbitrary-length uniform self-loop sweeps give a route to a compact proof of the late query. The trace has 6,803 macro instructions (3,402 ordinary blocks totalling 9,696 ordinary moves; 2,667 left sweeps and 734 right sweeps). The reusable packed checker and all 69 chunks of the 6,803-instruction trace have now passed local Lean RC2 against copied zipper definitions. The proof of the query has only propext, Classical.choice, Quot.sound. `PackedSweep.lean` imports the original ZipAuditCore; `generate_trace.py` emits the complete trace and weighted last-hole adapter. The original-source import and weighted adapter passed source-closure CI. Generate `Raw118Long.lean` via `python generate_trace.py > Raw118Long.lean`.

## Discovery reproduction
`discover.py` regenerates the initial partition, 5,065 FAR candidates (including the additional larger DFA bank and size-5 search), 67 delayed last-hole candidates and 679 sparse n-gram candidates. `generate_partial.py` emits a source-checkable partial audit with explicit residual leaves, retaining expensive long halts for separate compressed proofs.
Reuse agent2-tnf-raw99/enumerate.cpp, agent47-raw114-cut/seeded_far.cpp, agent7-far/large_far.cpp and agent47-raw111-cut/ngram_sparse.cpp. FAR bank is sorted union of agent47-raw112-cut/far-bank.txt, agent47-raw115-cut/far-bank.txt, and agent47-raw114-cut/all-far-bank.txt. Apply canonical size 4, then replay non-FAR tables to one million primitive moves; for the survivors try sparse n-grams through width 16 with a 200000-state cap.

SHA256 of newline-terminated open.txt: 00b82e8ded916fb719ebfd627d29da4bbf86659039b3b7889ff60a3f9ae396f9.
Tree JSON: 3d6425a04241b88e96a79f6ebc523592ad64b391cc114597e57831454291d8b5.
No global BB(6) improvement or parent certificate is asserted.
