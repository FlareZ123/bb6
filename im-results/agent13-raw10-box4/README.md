# Raw10 original rectangle 4: candidate exact weighted maximum 3640

The source-defined domain has fixed first six transition codes [8,14,11,7,17,4]; D0 excludes code 9, all other slots are unrestricted. It contains 234,375,000 machines. The exact weighted one-halt theorem reduces this to 46,116,864 representatives.

**Accepted source result:** [CI 45772207353](https://github.com/FlareZ123/bb6/actions/runs/45772207353) compiled Box4Core.lean and Box4Lower.lean, including sourceDomainEq, lowerBound and exact_of_slices, using standard axioms only. The machine [8,14,11,7,17,4,23,2,20,15,5,0] has 3639 live transitions plus the halt step and no incoming delay. The upper bound remains conditional on all six slice certificates.

**Complete computational classification:** 10,915 ngram invariant leaves, 1,096 symmetric RLE invariant leaves, 47 late halts, 3 translated cycles and 25 harder full-machine invariant candidates. The latter use 17 asymmetric lag-RLE and 8 block-FAR witnesses (survivors.json). Greedy enlargement and incidence quotient compress the 12,028 stack candidates to 3,882 safe boxes, covering 250,175 joint abstract states. A 722,569-node tree uses these banks, short halt and cycle witnesses, and 58 terminal long-trace/block witnesses. Every one-halt slice was computationally classified; no unresolved simulation timeout remains.

## Reproduction and proof status

Run `python im-results/agent13-raw10-box4/replay.py` after unpacking the coverage dependencies. The generated Box4Closure.lean will certify sourceBound and sourceExact if the complete Lean audit passes. The shared manual workflow agent13-coverage.yml provides weighted-tnf-raw10-box4-core/sample/full. Initial sample 45773059680 failed an import-name clash; 45773255508 regenerated the proof successfully but failed the missing zipHalt import in Box4Tree.lean, now fixed. The repaired [sample audit 45773874171](https://github.com/FlareZ123/bb6/actions/runs/45773874171) passed; the full generated certificate bank and closure still require a complete audit. No universal upper bound or parent Cover is asserted until that full audit accepts.

## Per-slice source-audit path

The aggregate full audit [45789352604](https://github.com/FlareZ123/bb6/actions/runs/45789352604) ended as cancelled after the Raw10 rectangle-4 step had run for essentially the full 60-minute job window. It did not accept the six-slice closure. Repeating the aggregate run unchanged would spend the same bounded CI window on all six independent trees.

The existing `agent13-coverage.yml` workflow now also offers `weighted-tnf-raw10-box4-slice`, with `box4_slice` selectable from 6 through 11. The replay accepts `--target N` and then:

- scans and classifies only the selected one-halt slice;
- filters the existing asymmetric-stack and block-FAR witness bank to that same final-halt slot;
- constructs a slice-specific safe-box bank and exhaustive first-hole tree;
- emits `Box4SliceN.lean`, whose theorem proves `Good N (root N)` for every machine in that slice.

Each accepted slice is a genuine source-connected partial Cover at bound 3640. It does **not** establish `sourceBound` for the whole rectangle; all six slice theorems are still required before `Box4Closure.lean` can be accepted. The aggregate target remains available for a sufficiently provisioned run.
