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

## Four new source-kernel-checked phase-aware BiDFA leaves (25 November 2026)

Stable zero-based leaves 1648, 2202, 2874, 5666 (622, 686, 436, 71 abstract configurations; 57, 64, 61, 28 stack edges) each have a single hole, thus cover 100 physical completions. These are new relative to the prior FAR, ngram, late-halt, symbolic, independent-counter, recursive and BiDFA candidate sets available at the claim commit. After those candidate sets and the four new witnesses, 87 one-hole candidate residuals remain, subject to full parent assembly. No change to the certified canonical frontier count yet.

TreeBiDFA.lean refines the existing BiDFA checker: successful lookup in a binary tree implies membership in its flattening, regardless of the key's injectivity or whether the tree is ordered; every node is checked, so TreeCheck.never invokes the original source-connected theorem. The generator balances the tree and emits independent subtree checks of at most eight states. Python/C++ candidate search is not trusted. Locally compiled each generated leaf independently with Lean 4.36.0-rc2, exact Git blobs Frontier 115438c4, Symmetry 84f62dce, RootShift 80b56fb0, SparseZipper 8081dc82, SweepPumping e518c288, BiDFA d0d1edb8, pinned claim commit 8599b132. All four final M*.never axioms: [propext, Quot.sound]. Local per-leaf compile times for 1648, 2202, 2874, 5666: 8.63, 8.78, 5.92, 1.23 seconds respectively. Generate one module via python tree_emit.py 1648 > Raw118Tree1648.lean (substitute index); or all four by omitting indices. New theorem namespace BB6Coverage.Agent16BiDFA.Raw118Tree.M{index}.never. Exact local checked source blob TreeBiDFA c75d8ab4d18ced55a3b1c70cf99cbe7530c537b2, generator 255f9ffff7534c904033ee626558be063b2a03c2.

Discovery: asymmetric stack DFA summaries with suffix bits, phase modulo m, reset on a two-/three-bit marker, modular counts of patterns (including three-bit words), optional initial prefix. 1648/2202 use (left k=4, m=2, reset on 110, right k=5 plain); 2874 uses (left k=4 m=2 reset on 100, right k=5 m=2 count 111); 5666 uses (left k=2, m=2, initial prefix length 2, right k=3 m=2). Search details and residual roster will be preserved separately. This is not yet a raw118 parent proof.


## Two original-source accepted nested-restoration leaves (25 November 2026)

Leaves 655 and 657 of the fixed open.txt roster have distinct one-hole tables and admit universal nonhalting proofs by nested strong induction:

| Leaf | Exact partial table | Right word of growing F-section | Original-source CI |
|---|---|---|---|
| 655 | `1RB1LA_1RC1RB_0RD0LA_1LD1RE_0RF0LE_0RB---` | `0 1^(n+1)` | [45685852382](https://github.com/FlareZ123/bb6/actions/runs/45685852382) |
| 657 | `1RB1LA_1RC1RB_0RD1LA_1LD1RE_0RF0LE_0RB---` | `(01)^(n+1)` | [45686057730](https://github.com/FlareZ123/bb6/actions/runs/45686057730) |

Both have left zipper `0^(n+2) S`, where the left zipper includes the head, and enter the n=0 family after 24 ordinary transitions with fixed suffix S=010100. Define a section F(n,S,R) by appending arbitrary right tail R to the indicated right word. Leaf 655 has a positive run F(n,S,00R) → F(n+1,S,R); leaf 657 has F(n,S,000R) → F(n+1,S,R). The reset erases a run of 2n+3 or 3n+4 zeros respectively, leaving a marker 1; a 9-step seed and successive smaller nested restoration calls establish the general rule by strong induction on n. The empty-right boundary has a separate exact proof F(n,S,[]) → F(n+1,S,[]), giving indefinitely many positive-cost returns.

The exact source modules [Raw118Nested655.lean](Raw118Nested655.lean) and [Raw118Nested657.lean](Raw118Nested657.lean) export `BB6Coverage.Agent16Raw118Nested.M655.never` and `BB6Coverage.Agent16Raw118Nested.M657.never`, each for every compatible total machine. Both original-source CI steps succeeded on Lean 4.36.0-rc2 with the no-sorry/no-native_decide guard. The local copied-model entry, closure and restoration lemmas also checked. These distinct leaves each represent 25 completions, i.e. 50 total conditional on the exact parent partition. No finite simulation cutoff is used in the proofs.

They are part of the remaining hard-set complement after the SAT, wide-window and run-aware candidate passes described in the [Agent40 dossier](../agent40-raw118-independent/README.md). The parent consumer must still explicitly incorporate these two certificates along with the other accepted leaves; this is not a complete parent cover.

## Source-closure status and exact residual accounting (25 November 2026)

The 274-row hard set after the extended FAR5 pass has a reproducible, pairwise-disjoint certificate partition:

- 105 symbolic pump certificates: source-accepted in [CI run 45640895310](https://github.com/FlareZ123/bb6/actions/runs/45640895310).
- 10 independent-counter certificates: source-accepted in [CI run 45600114599](https://github.com/FlareZ123/bb6/actions/runs/45600114599).
- 48 finite phase-graph certificates: source-accepted in [CI run 45601298658](https://github.com/FlareZ123/bb6/actions/runs/45601298658).
- 14 recursive-counter certificates: source-accepted in [CI run 45638645532](https://github.com/FlareZ123/bb6/actions/runs/45638645532), which compiles both the six-case and eight-case generators.
- 6 original BiDFA and 4 phase-aware TreeBiDFA certificates: source-accepted in [CI run 45637228733](https://github.com/FlareZ123/bb6/actions/runs/45637228733).

These are 187 distinct hard-set indices. The remaining 87 hard-set indices are all one-hole rows. `search_tree_bank.py` reconstructs the six source sets, asserts pairwise disjointness and containment in the 274-row hard set, checks the exact 87-row complement, and replays a bank of 26 previously successful two-sided DFA pairs against that complement. The new `weighted-tnf-raw118-treebank` target source-checks any additional certificates found by that replay.

The 959 residual leaves emitted by `generate_partial.py` are a different, larger parent-level set: 679 sparse n-gram rows + 274 hard rows + 6 delayed first-hole rows with more than 10,000 steps. The partial audit currently leaves all 959 unresolved because it consumes only FAR and short delayed-first-hole checks. Thus the 87 count is the exact complement *inside the hard set*, not yet the residual count of a Lean-checked parent consumer.

The 679 sparse n-gram certificates are being source-checked in [CI run 45642047107](https://github.com/FlareZ123/bb6/actions/runs/45642047107); do not count them as accepted until that run succeeds. Of the six long delayed-first-hole leaves, index 439 already has an original-source weighted certificate in [CI run 45575655393](https://github.com/FlareZ123/bb6/actions/runs/45575655393). `generate_late_traces.py` now constructs packed certificates for all six, but its expanded `weighted-tnf-raw118-long` target has not yet run.

`Raw118Consumer` and the `weighted-tnf-raw118-consumer` target now assemble the intended parent proof: consume 679 sparse + 187 hard-set + 6 long-first-hole certificates from the 959 residuals, then prove the exact remaining list has 87 one-hole tables (or fewer if the DFA-bank replay finds more). This is a target and generator, not yet a checked theorem. Likewise, `Raw118CanonicalMembership.lean` states that the parent is in the canonical 78-roster, but its source-closure run [45639243857](https://github.com/FlareZ123/bb6/actions/runs/45639243857) is still in progress; no membership claim is made until it succeeds.

No global BB(6) upper bound or completed Raw118 parent closure is asserted. The only established numerical constraint from this parent remains the 756,496 lower-bound witness.

## Two-phase restoration: leaf 10

The exact partial table `1RB1RA_1RC0RB_0RD---_1LD1RE_0LF0LE_1LA1LF` has an independent nonhalting certificate in [Raw118Nested10.lean](Raw118Nested10.lean), theorem `BB6Coverage.Agent16Raw118Nested.M10.never`. Original-source CI [45687301172](https://github.com/FlareZ123/bb6/actions/runs/45687301172) succeeded. The blank run enters state A with empty left zipper and right word `1^(4m+1)00001` at m=0 after 11 moves. Each root member returns to the next m by a two-phase strong induction: the two restoring cases for left zero gaps of lengths 4m+3 and 4m+4 transfer four zeros to four ones per pair of strictly smaller restoration calls. The base growth uses 38 ordinary transitions. The proof covers every compatible completion of the one-hole table; the exact source closure passed the axiom guard. This adds 25 physical completions to the two earlier nested leaves, conditional on the parent partition. No parent closure is claimed.
