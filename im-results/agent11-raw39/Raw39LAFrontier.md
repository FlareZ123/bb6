# Raw39 A1=0LA: normalized child frontier and run-length certificates

The literal child is `1RB0LA_1RC---_0RD---_1LD0RA_------_------`. A canonical first-hole traversal retaining all existing state labels and the least fresh label has 4,147 splits, 74,915 translated-cycle leaves, 18,644 last-hole leaves and 1,811 remaining open leaves at the original 1,000-step discovery horizon. Locally projecting the full original enumeration (149,785 cycles, 37,288 last holes, 3,621 open, 8,291 splits) exactly reproduced the normalized tree and open-list hashes. These are candidate classifications; the original Lean semantic checker must establish them.

## Candidate closure partition

- 1,661 FAR witnesses using the existing 77-code 1LB bank.
- 94 unequal-window witnesses, with widths and abstract-state counts in `la-frontier.json`.
- 44 finite bidirectional run-length/residue closure witnesses, independently regenerated in Python with the same reachable-state counts as the C++ discovery; closure sizes 29–3,866. A stack summary retains at most k recent runs, recording each run length exactly below a threshold c and modulo m thereafter (different parameters per symbol/side). The finite graph is constructed lazily, with observed predecessor edges. The existing `FastBiDFA.never` checker can consume each graph, independently of the search heuristic.
- One late final hole, normalized index 654, at step 1,002 (F0). Candidate weighted bound rises from 903 to at least 1,003. The final-hole weighted arithmetic and exact trajectory still require the original checker.
- Eleven genuine remaining candidate leaves: 146, 148, 162, 167, 714, 737, 952, 1362, 1479, 1718, 1719. Their exact tables are pinned in the data. The first four and 714/1719 show structured two-sided periodic growth; 737/952/1362/1479/1718 show apparent long right/left periodic trains and active counters. These are trajectory observations, not nonhalting theorems.

`prepare_raw39la_frontier.py` regenerates the exact normalized frontier and emits the candidate asymmetrical n-gram and run-length proofs using the existing 1LB emitters. It has not yet been executed as a whole against a source checkout; the Python run-length closure itself was executed on all 44 exact tables. The local toolchain is Lean 4.36.0-rc2, but local GitHub checkout is blocked by DNS. No new CI workflow or dispatch was created. Do not treat the candidate partition as an accepted Cover or global BB(6) progress until the remaining leaves and complete original-source consumer are proved.

The next step is the eleven actual residuals, preferably finite run-grammar/affine pumping or arbitrary-tail counter induction. No need to repeat the completed witness searches.
