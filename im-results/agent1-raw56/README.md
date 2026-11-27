# Raw56: source-checked local frontier (2026-11-27)

## Root query and conditional frontier

The six-hole parent is `1RB---_1RC---_0RD---_1LD1LE_------_------` (D1=1LE). Its first undefined query is E1 at ordinary time 6. Four ordinary choices (0LC, 0LD, 1LD, 1RD) close by immediate translated cycles. The remaining 20 canonical representatives are not assumed closed.

`Raw56RootCut.lean` passed original-source Lean 4.36.0-rc2 run [45883348983](https://github.com/FlareZ123/bb6/actions/runs/45883348983). Its `sound20` theorem proves the exact conditional parent partition at weighted bound 7,014: every compatible completion either has that bound or belongs to one of 20 canonical residual representatives. The distinguished E1=0RE child is exactly the six-hole table in `candidates.json`; `sound19` shows that accepting this child reduces the local residual list from 20 to 19. This is not a closed Raw56 parent or a global roster reduction.

## E1=0RE candidate certificate closure

Using the existing Agent7 Raw49 classifier at cap 1,000, lookback 32, depth 6, the child has 8,528 split nodes, 157,695 translated-cycle leaves, 35,737 last-hole leaves and 2,713 initially open leaves. The longest query was 762 and the longest detected cycle endpoint was 797.

All 2,713 open leaves have explicit candidate nonhalting certificates:
- 2,666 exhaustive FAR candidates with at most five DFA states;
- 23 larger FAR candidates with up to eleven DFA states;
- 20 source-generated symbolic sweep families;
- four sparse n-gram fixed points (widths 5, 9, 9, 13).

The last symbolic case, leaf 2006
`1RB0LF_1RC0RB_0RD0RA_1LD1LE_1LF0RE_1LA---`,
has the exact zipper candidate `A([], 1 (0101)^n 0101010101)`, entered at step 52. A return adds three copies of 0101 with cost 100+16n. The generic single-block discovery failed when the entire 12-bit increment was opaque; using a 4-bit transferable block exposed the recurrence. The generated sweep theorem checks arbitrary tails and induction.

## Source acceptance and composition

The source-accepted child theorem is
`BB6.Agent1Raw56.Raw56E1RE.all_quotient` at weighted bound **7,014**. The first source attempt [45882933157](https://github.com/FlareZ123/bb6/actions/runs/45882933157) failed because the C++ classifier serializes cycle direction as integer 0/1 while the inherited Lean emitter printed 1 as a Bool. `prepare.py` now validates the raw direction field and normalizes the private emitter copy; certificate data, tree bytes and hashes were unchanged.

The focused retry [45896758638](https://github.com/FlareZ123/bb6/actions/runs/45896758638) **succeeded**. It exported artifact `raw56-e1-0re-source-accepted`, ID **15155176780**, SHA-256 `bf260ccca509d044df18a538a3524387d7e1167ce50c15ae21d4c04630ff41ed` (220,460,371 bytes).

The first thin consumer attempt [45900392377](https://github.com/FlareZ123/bb6/actions/runs/45900392377) exposed a type mismatch between the generated child table and the hand-written refinement. `Raw56RootConsumer.lean` now proves the exact table equality with `sameTable_sound (by decide)` and transports the child theorem across it. The focused rerun [45912699461](https://github.com/FlareZ123/bb6/actions/runs/45912699461) **succeeded**: 747 project modules compiled; `child_table_eq` has axioms `[propext, Quot.sound]`; `sound19_closed` has axioms `[propext, Classical.choice, Quot.sound]`; and the strict checker accepted all seven profiles. It exported artifact `raw56-root-frontier-source-accepted`, ID **15160313745**, SHA-256 `6513147b3929ab6b707225b6592a882025e234d498ed8baca40216489b469b3d` (220,548,045 bytes).

No Raw56 parent Cover, full parent closure, global roster decrement or BB(6) upper bound is claimed. The global conditional baseline is maintained separately; this local Raw56 frontier does not alter that roster.

Since that 19-way root frontier was accepted, the E1=0RC residual has itself been completely source-certified at weighted bound **10,000**. Run [46045652695](https://github.com/FlareZ123/bb6/actions/runs/46045652695) accepted every one of its nineteen literal C1 branches and the final theorem `BB6.Agent1Raw56Root.sound18RC_closed`, leaving **18** Raw56 root residual representatives under the raised common bound 10,000. Final artifact `raw56-rc-final-source-accepted` is ID **15223571643**, SHA-256 `bf35d6ab4db0678da3ad4adaa4577dce4507b8f530d3204ef4c0522d4babd050`. Separately, E1=0LE has a source-accepted 14-to-12 internal reduction for its E0=0RB and E0=0RC children; see [le/README.md](le/README.md). E1=0LE is not yet a complete child Cover, so it does not further reduce the 18-way root frontier.

## E1=0RC: complete source-accepted child at bound 10,000 (2026-11-27)

The E1=0RC child first queries C1 at time 7. `Raw56E1RCCut.lean` proves five translated-cycle closures and a 19-way literal residual frontier. `Raw56E1RCMixed.lean` assigns branch-specific bounds—7,014 to eighteen branches and 10,000 to the late 0LF branch—and `Raw56E1RCAll.lean` imports all nineteen exact child proofs. The source-accepted theorem `BB6.Agent1Raw56E1RC.all_quotient` gives the whole child weighted bound 10,000; `BB6.Agent1Raw56Root.sound18RC_closed` then removes this child from the previously accepted 19-way Raw56 root frontier.

The completed table is `1RB---_1RC---_0RD1RD_1LD1LE_---0RC_------`. At cap 1000, lookback 32 and depth 6 the first-hole tree contains 791 splits, 15,146 cycle leaves, 2,946 last-hole leaves and 102 open leaves (no aliases). The maximal query and cycle-end times were 567 and 917. Of the open leaves, 98 have FAR witnesses with at most five states, three use witness 1012345214422, and the final leaf at zero-based index 3 has an explicit growth proof.

For M3 (`1RB0LF_1RC0LB_0RD1RD_1LD1LE_0LA0RC_---1LA`), let the A-state zipper have left stack 011 and right stack 0111(01)^n00R. The exact transition over 48+14n steps sends (n,R) to (n+1,11R), for arbitrary R. The blank entry at step 83 has n=0 and R=1111. Rightward 12-step transfers, a 12-step and 9-step turn, leftward 2-step transfers, and a 21-step return establish this recurrence; `never_of_growth` gives nonhalting for every compatible completion. This is formalized in `Raw56RC_RD_M3.lean`.

Original Lean 4.36.0-rc2 was reconstructed locally. The base is the source-accepted 747-module artifact 15160313745 above, with all manifest olean hashes checked. All 57 generated modules compiled against that base. `BB6.Agent1Raw56.RCRD.all_quotient` and `.all` prove weighted bound 7014; `BB6.Agent1Raw56E1RC.sound18_closed` proves the conditional child refinement. These three theorems have axioms [propext, Classical.choice, Quot.sound]; the M3 growth and never theorems and the table equality have [propext, Quot.sound]. No sorry or native_decide dependency. Source commit f7f26307250bf1f91462a5d4701c96031b29b9a7 contains the exact locally compiled handwritten sources and emitter.

### Additional E1=0RC branches: C1=0RD and C1=1LE

[Four source-checked unary sweep leaves](UnarySweepLeaves.md) resolve the four hard individual machines left after FAR6 and sparse fixed-point discovery. The width-8 sparse witness (346 joint configurations, 19 left and 29 right edges) also compiled. Both complete branch certificates have passed all 126 generated modules against the pinned source-accepted base with Lean 4.36.0-rc2. `BB6.Agent1Raw56.RC0RD.all_quotient` and `BB6.Agent1Raw56.RC1LE.all_quotient` prove weighted bound 7014, as do their `.all` variants. `Raw56E1RCUnaryConsumer.lean` proves exact table equalities and `sound16`, conditional only on the previously source-checked `1RD` theorem. The 16-member intermediate list has an explicit `count16` proof. These branches were subsequently incorporated into the successful all-nineteen assembly in run 46045652695. The complete branch theorems and the final mixed-bound/root-consumer chain use only the standard repository axiom profile `[propext, Classical.choice, Quot.sound]`; the final source-accepted artifact above supersedes the earlier local-only wrapper status.

`prepare_rc_unary.py OUT` regenerates both cuts and FAR banks with SHA-256 pins, plus the sparse data via Agent47's exact emitter; compile the four handwritten leaf modules and `UnarySweep` first, then each generated manifest and the consumer. The source-checked local refinements do not reduce the global roster. Discovery has also exposed a late C1=0LF query at 9474 steps, so any complete E1=0RC proof must use a larger weighted bound than 7014.

## Complete candidate coverage of the other sixteen C1 choices

See [Portfolio.md](Portfolio.md) for the exact replay spec, combined abstraction method, and mixed-bound requirement. Every remaining C1 choice was candidate-complete and is now included in the source-accepted all-nineteen proof-object union from run 46045652695. The exact mixed-bound composition proves the complete E1=0RC Cover and the root 19→18 adapter at bound 10,000. Raw56 itself remains open because the other 18 root residual representatives are not all covered.

## Reproduction of C1=1RD

Run `python im-results/agent1-raw56/prepare_rc_rd.py /tmp/raw56-rc-rd` from the repository. Compile M3 and the generated modules in the order of generated/manifest.json with the accepted base artifact on LEAN_PATH, then the cut and consumer. The exact original classifier and FAR source blobs are checked by the preparation script. The tree, open list, exhaustive FAR and combined witness bank SHA-256 digests are pinned in the script. The candidate computation is untrusted; the universal bound comes from the kernel-checked canonical certificate and source semantics.

## Reproduction

Run `python im-results/agent1-raw56/prepare.py` to regenerate the deterministic child sources. The manifest pins tree and open-list bytes, exhaustive FAR output, larger FAR automata, exact pump indices and sparse fixed-point sizes. Compile `im-results/agent1-raw56/generated/Raw56E1REAll.lean` through `tools/lean_compile_closure.py` after the normal shared-core unpack and sweep generation. The existing manual Raw57-sibling workflow selectors are `raw56-e1-0re` and `raw56-root-consumer`; the latter takes the successful child run ID as `source_run_id`.
