# Raw56 E1=0RE: source-checked local frontier (2026-11-26)

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

The new `Raw56RootConsumer.lean` consumes that exact child theorem through the precompiled manifest and supplies it to `Raw56RootCut.sound19`. The thin consumer run [45900187499](https://github.com/FlareZ123/bb6/actions/runs/45900187499) is currently in progress. If accepted, it will source-check the conditional 19-residual frontier without recompiling the child's dependency closure.

No Raw56 parent Cover, full parent closure, global roster decrement or BB(6) upper bound is claimed. The global conditional baseline is Canonical58 after the Raw113 integration; this local Raw56 frontier does not alter that roster.

## Reproduction

Run `python im-results/agent1-raw56/prepare.py` to regenerate the deterministic child sources. The manifest pins tree and open-list bytes, exhaustive FAR output, larger FAR automata, exact pump indices and sparse fixed-point sizes. Compile `im-results/agent1-raw56/generated/Raw56E1REAll.lean` through `tools/lean_compile_closure.py` after the normal shared-core unpack and sweep generation. The existing manual Raw57-sibling workflow selectors are `raw56-e1-0re` and `raw56-root-consumer`; the latter takes the successful child run ID as `source_run_id`.
