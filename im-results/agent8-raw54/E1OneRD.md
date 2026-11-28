# Raw54 E1=1RD: Lean-certified samples and candidate-pruned frontier

**Status:** intermediate research, not a complete Raw54 weighted bound or a BB(6) solution.

## Target

Raw54 E1=1RD is the first-hole child with machine code
1RB---_1RC---_0RD---_1LD0LE_---1RD_------.
It equals the Raw54 parent refined at slot (4,true) with move ⟨true,true,3⟩.

## Original-source Lean theorem

[Raw54OneRDFAR128.lean](Raw54OneRDFAR128.lean) contains 128 explicitly coded
partial machines. It decodes each from a base-25 integer (slot digit 24
means unassigned), validates a 1-state or 2-state FAR DFA using the original
FAR.fastTryDfa and checks that the partial machine refines the actual parent.

Lean 4.36.0-rc2 locally accepted the eight 16-case kernel verification
batches and the two universal theorem families: **samples_never**, asserting
that every compatible total machine is nonhalting, and **samples_parent**,
asserting compatibility with the Raw54 E1=1RD parent. Source axiom audit
showed only propext, Classical.choice, Quot.sound. The independent
[original-source CI check](https://github.com/FlareZ123/bb6/actions/runs/46122224331)
**succeeded**. These 128 explicitly enumerated cases are a rigorous
source-accepted partial result, not a complete coverage theorem.

## Computational FAR-pruned frontier (not Lean-certified yet)

At a first-hole enumeration cutoff of 1,000 steps, the unpruned source
simulator had 38,180 open nodes, 232,344 cycle nodes, 77,398 last-hole
nodes and 15,127 split nodes. A bank of 169 distinct source-extracted
two-sided FAR automata from the E1=0RC source-accepted artifact
([run 46088429391](https://github.com/FlareZ123/bb6/actions/runs/46088429391))
and E1=1RC generated Lean sources
([run 46102720259](https://github.com/FlareZ123/bb6/actions/runs/46102720259))
matched 37,509 of 38,180 originally open tables.

The exact bank is [oneRD_leancert_bank.txt](oneRD_leancert_bank.txt).
[oneRD_pruned_far.cpp](oneRD_pruned_far.cpp) adds FAR tests at *internal
tree nodes* before spending computation on descendants. Reproduce:

~~~sh
g++ -std=c++17 -O3 im-results/agent8-raw54/oneRD_pruned_far.cpp -o /tmp/onerd-far
mkdir -p /tmp/onerd-test
(cd /tmp/onerd-test && /tmp/onerd-far '1RB---_1RC---_0RD---_1LD0LE_---1RD_------' /path/to/repo/im-results/agent8-raw54/oneRD_leancert_bank.txt)
~~~

This command generates open.txt and tree.json in the current directory.
The observed mass ledger is:

| Pruned classification | Nodes | Completion mass |
| --- | ---: | ---: |
| FAR candidate | 262,326 | 224,161,350 |
| Side cycle | 7,527 | 422,175 |
| Direct halt | — | 17,674,973 |
| Last-hole terminal bound | 77,398 | 1,857,552 |
| **Residual open** | **671** | **24,575** |
| **Total** | — | **244,140,625 = 25^6** |

The 671 residual open nodes comprise 658 with one hole and 13 with
two holes: 658 × 25 + 13 × 625 = 24,575 remaining total-machine
completions in this counting convention. The original open mass was
21,730,100; FAR candidates cover 21,705,525 of that mass (99.887%).
A cutoff-limited maximum score of 992 is **not** a mathematical upper
bound on the full cylinder.

Reproducibility SHA256:
* original open.txt: 1c83c32efa5aec9d91e60963a67198199c8b4f1363fa375ab07873e59db0e87e
* pruned open.txt: 751a7ffed5bc8def90461cbb152e6521779fc45018cd0ed7de0312d4e25f4385
* bank file: 37dca6055038f1128d72fd840e559dec2f97233485889797518d461bd1efdbc9

**Research boundary:** the complete pruned-tree result remains
computational evidence. The 128-case Lean theorem is source-accepted;
this dossier makes no claim to certify the other FAR hits or close the
671 residual leaves. The next step is compositional source replay of
the ancestor-pruned tree using the existing Lean Audit/fastFAR checker.
