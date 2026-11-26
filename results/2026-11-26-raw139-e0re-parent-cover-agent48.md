# Raw139 E0=0RE: a source-accepted six-hole parent Cover at weighted bound 852

## Theorem

Let (p) be the six-hole partial two-symbol, six-state machine with slot-code vector

[
[7,24,11,24,14,24,24,16,17,11,24,24],
]

in slot order (A0,A1,ldots,F0,F1), where code (24) denotes an unassigned transition and the remaining codes use (4q+2w+d). This is the Raw139 E0=0RE parent, normalized address ((2,langle false,true,4angle)).

For every total six-state, two-symbol machine (M) compatible with (p), the universal weighted halting bound holds:

[
orall M,quad ppreceq M Longrightarrow operatorname{WeightedBound}(852,M).
]

The original-source Lean theorem is `BB6.Agent48Raw139E0ZeroRE.all_completions_weighted`. The parent Cover is complete: it quantifies over every compatible total completion, not merely the finite leaves sampled by the discovery search.

## Proof construction

The proof begins with a first-hole partition of the 12-slot parent. The reproducible partition has 11,690 internal splits, each retaining all 24 ordinary transitions. The 268,871 terminal leaves are partitioned into 216,456 cycle leaves, 41,264 last-hole leaves, 10,416 ordinary FAR leaves, and 735 separately proved leaves.

The discovery census initially left 736 open leaves. The committed compact manifest and replay generator reproduce their exact classification:
- 734 Block-FAR certificates;
- one final-hole F0 leaf first reached at step 846;
- one inductive sweep leaf.

The final-hole proof uses a head-inclusive reverse-left zipper. Its symbolic family (X(n,k,h)) admits the exact recurrence
(X(n,k,h)	o X(n+1,max(k-3,0),h-1)) in (20n+75) steps. The recurrence preserves arbitrary untouched tails, so the unassigned B1 transition cannot prevent an unbounded live run. The proposed bound is (846+6=852).

The discovery/replay path is preserved in [Agent48's reproducibility dossier](../im-results/agent48-raw139-e0-0re/README.md), including `spec-compact.json`, `replay.cpp`, `package6.py`, and `reproduce-parent.sh`. The replay was compared against the established scanner on 120 seeded small fixtures; the complete generated dependency graph is reachable and acyclic.

## Formal verification

The complete parent proof passed original-source Lean 4.36.0-rc2 CI:

- [Run 45799738861](https://github.com/FlareZ123/bb6/actions/runs/45799738861), pinned source checkout `4fd22a0575df518a25844ec74755b61db17c1f54).
- 423 project modules compiled.
- Accepted root theorem: `BB6.Agent48Raw139E0ZeroRE.all_completions_weighted`.
- The `hRoot` and `all_completions_weighted` axiom profile is `[propext, Classical.choice, Quot.sound]`.
- Accepted artifact: [15110025526](https://github.com/FlareZ123/bb6/actions/runs/45799738861/artifacts/15110025526), SHA256 `51880d101ca787263f9122059373c367d80d1b1523f308e333d532915cc7a55b`.

The symbolic last-hole nonhalting component also has a separate original-source audit, [run 45799689607](https://github.com/FlareZ123/bb6/actions/runs/45799689607), but the parent theorem above is independently accepted by run 45799738861.

## Scope and remaining dependency

This theorem closes the E0=0RE six-hole parent cylinder at bound 852. It is a genuine universal Cover, not a heuristic classification or an exact BB(6) result.

The normalized Raw139 roster identifies this parent at address ((2,0RE)). The exact refinement relation from this parent to the current active Canonical64 Raw139 leaves is being integrated in [the normalized crosswalk](../im-results/agent14-raw139-d0-generic/Canonical64Raw139NormalizedCrosswalk.lean). Until that crosswalk is source-compiled and its fanout inspected, no reduction in the 64-way Canonical64 roster or the active Raw139 complement is claimed. The global BB(6) upper bound remains open.
