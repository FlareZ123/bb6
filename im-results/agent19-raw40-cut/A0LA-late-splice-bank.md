# Late blank-frontier splice bank

Exact one-, two- and three-pump certificates for all eleven residuals from the compressed 0LA frontier recipes. Each row is an authentic blank replay, exact base epoch, equality of chronological edge-crossing lists at each cut, and a normalized symbolic word identity for all pump exponents, using the [crossing-splice lemma](../agent42-raw40-crossing-splice/README.md). The independent [finite premises checker](check_late_splice_bank.js) passes all eleven rows. `side: R` mirrors spatial coordinates before recording cuts; shift is always in physical coordinates. The final row starts and ends in state C reading blank; all other rows use A reading blank. These are mathematical certificates awaiting source-level Lean acceptance, not a global decrement.

| Child/leaf | Entry | Head | Epoch | Shift | Cuts (oriented) | Increment |
|---|---:|---:|---:|---:|---|---:|
| 0LE/366 | 729 | -15 | 494 | -6 | [[3,15]] | 112 |
| 0RE/759 | 1243 | -15 | 1466 | -8 | [[3,23]] | 544 |
| 0RE/792 | 1129 | -15 | 1312 | -8 | [[3,23]] | 480 |
| 0RE/1730 | 20104 | 80 | 48572 | 60 | [[9,229]] | 28800 |
| 0RE/1736 | 19128 | 80 | 46006 | 60 | [[9,229]] | 27200 |
| 0RE/790 | 2198 | -48 | 444 | -8 | [[15,17],[30,36]] | 30 |
| 1RE/390 | 23992 | -132 | 19302 | -50 | [[2,42],[133,143]] | 5600 |
| 1RE/1179 | 23992 | -132 | 19302 | -50 | [[2,42],[133,143]] | 5600 |
| 0RE/627 | 135300 | 1004 | 19958 | 96 | [[9,33],[688,760]] | 912 |
| 0RE/1403 | 133274 | 1004 | 19728 | 96 | [[9,33],[688,760]] | 912 |
| 1RE/1096 | 483904 | 1298 | 271120 | 336 | [[1,225],[907,1003],[1253,1269]] | 60256 |

The exact parametric epoch cost is `period + increment*n`. The normalized word identity equates the pumped final tape with the next member of the pumped entry family, including the physical head displacement. The same proof applies to every completion of the missing transition. Discovery sources: [one pump](late_splice_search.js), [two pumps](late_splice_multi.js). The two-pump discovery matches both insertions at a common pair of frontiers and uses the actual edge crossings, not just apparent growth.

## Final residual 1RE/1096

At state C reading blank at the right frontier, let the word be written leftward from the head. After 483904 ordinary moves, the head is at 1298 and the word is exactly `0^865 111 P (00000111)^40 0^9 111 0^11 111 B T`, where `P=011111101111111100011101110000111111111`, `B=0000011111100111`, and `T` is the remaining fixed suffix. A 271120-step epoch advances the head by336 and increases the three exponents by224,12,1 respectively. The actual chronological boundary lists agree at the three cuts [1,225], [907,1003], [1253,1269], with total additional departure count60256 per simultaneous pump. The independent checker derives the entire endpoint words from the literal transition table and checks their normalized identity, not just these exponents. Thus the exact unbounded recurrence has cost `271120+60256*n`. The phase was identified by sampling every sixteenth right-frontier C0 return; the third growing block repeats after seven of these coarse returns. The discovery required growth of336 cells, outside the earlier two-pump search limit256. All eleven residuals are now mathematically covered.

## Source integration candidate: orientation and non-A return
All twelve mathematical splice certificates (eleven above and the separate [0RD/154](A0LA0RD-leaf154-two-pumps.md)) now have explicit source-consumer declarations. [Raw40OrientedCrossing.lean](Raw40OrientedCrossing.lean) reuses Agent42's existing script soundness and word normalization, rather than copying or changing the kernel checker. It transports a full original machine through an involution (optional reflection and optional A/C swap), then supplies an explicit transformed blank entry state. The key point for 1RE/1096 is that its transformed initial state is C, not A; the repeated section starts in transformed A, corresponding to original C. No root state is silently changed.

The [orientation-aware executable preflight](preflight_oriented_crossing.js), run in the JS tool on the twelve literal records, passed all 12 transformed blank entries, exact endpoint states/heads, symbolic power normalizations, and departure increments. This tests the new transformation/normalization interface, not a new nonhalting discovery. The original finite crossing checks remain necessary. The candidate Lean consumers are split by check cost: [short](Raw40LateCrossingShort.lean) four, [long](Raw40LateCrossingLong.lean) seven, and [triple](Raw40LateCrossingTriple.lean) one. The last has 483904 entry and 271120 epoch moves and may need chunked kernel reduction; do not rerun discovery if it does. Compile the exact existing Agent42 CrossingCore/Bank/Source/Generate chain first, then Raw40OrientedCrossing, then Short, Long, Triple. Import and audit each exported never theorem; use existing source integration workflow, no new per-leaf CI. A kernel diagnostic must be repaired before repeating the target.

Status: source **candidate**. Local container returned ClientError before echo or Lean bootstrap; Python runtime creation returned TooManyActiveSessionsError. The separate Actions MCP manual trigger is available. Focused [Lean preflight 46059937656](https://github.com/FlareZ123/bb6/actions/runs/46059937656) pinned `7511a59b9ad9eaffabef91bb983dc0b8356c11da` and successfully compiled Frontier, Symmetry, RootShift, SparseZipper, CrossingCore, CrossingBank, CrossingSource and CrossingGenerate. First actual diagnostic was Raw40OrientedCrossing.lean:71:42, a conjunction of head-coordinate equality and reflexive tape function equality in `move_orient`. The proof now splits that conjunction, cases on direction and reflection, and uses omega/rfl. The focused repair still needs acceptance; no concrete leaf or parent Cover is accepted.
