# q32 five-hole batch

Four exact queue rows have complete candidate trees. The classifier uses ordinary first-hole splitting, translated cycles, final-hole bounds, a small fixed DFA bank, and all-length sweep proofs emitted by the existing Agent31 generator.

| Queue row | Bound | Splits | Cycle | Last-hole | FAR | Symbolic |
|---|---:|---:|---:|---:|---:|---:|
|28|131|907|15779|4572|487|24|
|35|242|682|11909|3262|504|12|
|36|198|1870|32194|9998|809|10|
|37|106|759|13397|3734|327|0|

Rows are identified by the original literal q32 queue and not a reordered residual list. All finite classifications and the final symbolic proof leaves must pass the original Lean audit. Counts were measured in local discovery; row 36's final bank uses 22 DFAs of width 4–6. All ten remaining machines admit one-parameter sweep proofs, with actual entry and return cost discovered from their traces. The generator records each exact residual, entry, intercept and slope and uses the original `.proven` constructor to tie each proof to its leaf.

The targeted manual workflow is `weighted-tnf-q32-five-hole`. These are candidate closures until the matching audit succeeds. Neither this batch nor the earlier accepted rows can close the entire raw11 parent without handling its actual complement.
