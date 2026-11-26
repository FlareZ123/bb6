# Raw139 E0=0RE: source-accepted parent Cover at weighted bound 852

Exact parent `[7,24,11,24,14,24,24,16,17,11,24,24]` (A0,A1,...,F0,F1; code 4q+2w+d; 24 unassigned). This is a distinct six-hole depth-two sibling, not any C1, D0 or F1 descendant.

A first-hole census with translated cycles through 450 steps and ordinary FAR d≤2 produced 11,690 internal splits, 216,456 cycle leaves, 41,263 last-hole leaves, 10,416 FAR leaves and 736 open leaves. The maximum first-hole time in the census was 193. All 736 opens have now been classified computationally: 734 Block-FAR certificates (widths 2/3), one final hole F0 at step 846, and the exact inductive sweep below. Candidate weighted bound 852 = 846+6. The full parent Cover is now source-accepted.

## Exact symbolic last leaf

Table `[7,21,11,24,14,23,3,16,17,11,15,20]` has only B1 unassigned. With the head-inclusive reverse-left zipper, let X(n,k,h) be state A at h, left [0,1,1], right 0^4 1^(4n) 0^k, both sides zero padded. Blank enters X(0,17,-4) at step 636.

The exact recurrence is X(n,k,h) → X(n+1,max(k−3,0),h−1) in 20n+75 steps. Its decomposition: 26 preparation steps; 2n right-moving pair macros of four steps; five turning steps; 4n+8 left-moving one-symbol macros of three steps; 20 finishing steps. All these macros preserve arbitrary untouched tails. Iteration yields an unbounded live run independently of B1. In particular after j complete cycles the elapsed step count is 636+10j²+65j.

The original-source audit is **accepted**: run [45799689607](https://github.com/FlareZ123/bb6/actions/runs/45799689607), source checkout 4fd22a0575df518a25844ec74755b61db17c1f54. All 49 project modules compiled; growth, arbitraryRun and never use only propext and Quot.sound, first only propext. The artifact is 15106203345. The bridge handles the definitional equality of blank and emptyAt 0 explicitly. Thus every completion of this exact last leaf is nonhalting.

## Reproducible complete parent candidate

The previous census lacked committed leaf recipes. The compact manifest `spec-compact.json` now records every open leaf's classification, and `replay.cpp` shares already checked prefixes while enumerating the same split tree and preserving the original scanner's witness order. Its entire output matched the established scanner on 120 seeded small fixtures. The complete replay took 2.02 s locally and recovered the exact earlier census. Partition SHA256: `30ac13a27cc0d4571f8f3010433994d90831d3edaacd683f5ba3adc889e31641`.

The 268,871 ordinary terminal leaves are exactly 216,456 cycle, 41,264 last-hole (including late leaf 447), 10,416 ordinary FAR, and 735 separately proven leaves (734 Block-FAR plus sweep leaf 734). The 11,690 internal nodes each retain all 24 ordinary transitions. All 736 previous opens have reproducible recipes. The late final hole F0 is first reached at step 846; the proposed bound is 852.

`package6.py` generates the original FastThreeHoleAudit certificate, splitting the large tree into sibling groups capped at 1800 leaves where possible, with 92 Block-FAR modules, 276 branch modules and one root. The complete generated dependency graph is reachable and acyclic. From repository root run `bash im-results/agent48-raw139-e0-0re/reproduce-parent.sh` with Lean 4.36.0-rc2. This uses the existing exact-source closure builder and axiom audit, including the original first-hole/weighted semantics and original FAR/Block-FAR checkers. No native-decide or sorry-dependent theorem is accepted.

**Full parent status: ACCEPTED.** CI [45799738861](https://github.com/FlareZ123/bb6/actions/runs/45799738861) succeeded with source checkout `4fd22a0575df518a25844ec74755b61db17c1f54`. The exact theorem `BB6.Agent48Raw139E0ZeroRE.all_completions_weighted` proves every completion of the parent table is `WeightedBound 852`. The exact-source closure compiled 423 project modules; `hRoot` and `all_completions_weighted` depend only on `propext`, `Classical.choice`, and `Quot.sound`. The accepted artifact is [15110025526](https://github.com/FlareZ123/bb6/actions/runs/45799738861/artifacts/15110025526), SHA256 `51880d101ca787263f9122059373c367d80d1b1523f308e333d532915cc7a55b`. This establishes the parent Cover, but does not by itself establish that it refines any active Canonical64 Raw139 leaf; the normalized crosswalk must still be compiled and inspected.

The normalized residual address is (2, 0RE), i.e. (2, ⟨false,true,4⟩), from Raw139Normalized.p2. It is not in the original normalized acceptedRows or witnesses, and is distinct from the discharged E0=0RA row. The exact table transport and current active-list consumer should be checked in the normalized roster integration; no count reduction is claimed here.
