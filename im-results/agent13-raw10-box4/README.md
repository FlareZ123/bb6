# Raw10 original rectangle 4: candidate exact weighted maximum 3640

The source-defined domain has fixed first six transition codes [8,14,11,7,17,4]; D0 excludes code 9, all other slots are unrestricted. It contains 234,375,000 machines. The exact weighted one-halt theorem reduces this to 46,116,864 representatives.

**Accepted source result:** [CI 45772207353](https://github.com/FlareZ123/bb6/actions/runs/45772207353) compiled Box4Core.lean and Box4Lower.lean, including sourceDomainEq, lowerBound and exact_of_slices, using standard axioms only. The machine [8,14,11,7,17,4,23,2,20,15,5,0] has 3639 live transitions plus the halt step and no incoming delay. The upper bound remains conditional on all six slice certificates.

**Complete computational classification:** 10,915 ngram invariant leaves, 1,096 symmetric RLE invariant leaves, 47 late halts, 3 translated cycles and 25 harder full-machine invariant candidates. The latter use 17 asymmetric lag-RLE and 8 block-FAR witnesses (survivors.json). Greedy enlargement and incidence quotient compress the 12,028 stack candidates to 3,882 safe boxes, covering 250,175 joint abstract states. A 722,569-node tree uses these banks, short halt and cycle witnesses, and 58 terminal long-trace/block witnesses. Every one-halt slice was computationally classified; no unresolved simulation timeout remains.

## Reproduction and proof status

Run `python im-results/agent13-raw10-box4/replay.py` after unpacking the coverage dependencies. The generated Box4Closure.lean will certify sourceBound and sourceExact if the complete Lean audit passes. The shared manual workflow agent13-coverage.yml provides weighted-tnf-raw10-box4-core/sample/full. Initial sample 45773059680 failed an import-name clash; 45773255508 regenerated the proof successfully but failed the missing zipHalt import in Box4Tree.lean, now fixed. The repaired sample 45773874171 is pending at time of writing. No universal upper bound or parent Cover is asserted until that full audit accepts.
