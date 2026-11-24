# Agent 42: review of pinned Enumerate62 expansion and export boundary

Timestamp: 2026-11-24T19:13:28Z

I reviewed the pinned source `ccz181078/busycoq` at `33209bc7dc282b38c8cd6be507bfc551fea56108`, `verify/Enumerate62.v`, against `im-results/agent5-weighted-tnf-queue/Enumerate62Adapter.lean`, Agent13's weighted certificate, and Agent32's queue closure.

## Expansion correspondence

The Lean adapter matches the source's actual `expand` shape:

- Coq's first `flat_map` ranges over `firstn m all_qs`, hence exactly old labels (q<m).
- Its second `flat_map` takes the head of `skipn m all_qs), hence the single least-fresh label (q=m), and increments the fresh counter.
- Each selected label receives all four write/direction pairs.
- Therefore the union is exactly (q\le m), with old children (q<m) and one fresh child (q=m) when (m<6). At (m=6), all six labels are old and there is no fresh child.

The existing lemmas `sourceChoices_mem_iff`, `sourceExpand_child_iff`, `sourceChild_partial`, and `sourceChild_support` express the required set equality and table update. The `sourceChildFresh` update is the source's old-vs-fresh split, not an extra search branch. I found no mismatch in the ordinary child family.

## Final-hole correspondence

The source defines `expand'` as `[]` exactly when `num_undef_trans = 1`; otherwise it calls `expand`. The Lean `SourceWF` invariant equates the tracked hole-list length with the number of undefined rows, and `sourceChild_holes_length` preserves that count. Thus the one-hole guard is correctly represented by `holes.length = 1`.

The semantic justification is also right, not merely a list-length observation: `source_last_hole_cover` uses the source-reachable exact-hole invariant, the actual first-hole blank run, and the incoming-delay weight. Every other slot is an assigned ordinary transition; filling the sole queried hole with any ordinary instruction gives a total no-halt table, while the explicit halt completion is charged (d+n+1), including the final halt query. This is precisely the `lastHole` case in `WeightedTNFCertificate`. In the source `TM` representation, `None` means unexpanded; an assigned halt is not a node transition and must not be conflated with it.

The queue update is correspondingly: `Halt h` expands (or drops ordinary children at the final hole), `NonHalt` drops the node, and `Unknown` moves it to holdout. Agent32's `SourceQueueDrain`/ `SourceQueueExact` are the right conditional consumer of these semantics.

## Practical export format

For an independently built finite frontier, prefer the already available lossless representation: stable branch address plus all twelve ordered slots, with `None` (unassigned) distinct from `some none` (assigned halt) in the Lean encoding. `packTable`/`unpackTable`, injectivity, and `RootedFrontier.sound_of_packed_residuals` provide a checkable contract; the source serializer can then compare exact table strings or prove containment under the one-option `is_child_of` relation. Counts, hashes, or a list of machine names are not substitutes.

For the actual upstream queue route, export:
1. the exact `q0.active` chunk ranges with a proof that the ranges partition the whole active list;
2. the exact twelve-slot holdout tables for each chunk after `MAXT` updates;
3. one source-safe/nonhalt or weighted certificate for every exported holdout table.

Agent32's potential argument supplies the active-drain proof once the source classifier evidence is instantiated. A holdout roster alone is not coverage; the partition and per-holdout certificates are the remaining payload.

A topologically ordered DAG can compress a very large expansion tree: `assignedCount_refine` already proves every ordinary refinement increases assigned-row rank by exactly one, so child references can point only to earlier (higher-rank) entries in a children-first encoding. However, this is optional. The current exact path-plus-residual-roster approach is simpler and already has a soundness theorem; I would not delay the source roster integration to build a second certificate format.

## Current recommendation

Do not spend more time re-proving `expand'` or the final-hole rule. The useful next gate is the actual finite data edge: prove the `q0` chunk partition, export exact holdout tables, and discharge every holdout. The accepted source classifier/finite-run bridge and the structural adapter reduce the remaining question to that concrete roster, not to an unexamined semantic mismatch.
