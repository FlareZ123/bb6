# Raw125: complete candidate classification of a six-hole parent

Parent: `1RB---_1RC---_0RD---_1LD1RE_---1RF_------` (canonical roster raw index 125). The first hole is F1 after 7 ordinary transitions. The target is a source-level `Cover (WeightedBound 1290)` for all 25^6 = 244,140,625 completions, not merely a list of observed nonhalters.

## Candidate search (complete, not yet kernel accepted)

The exact cycle/first-hole enumerator from agent11-raw121/fast_enum.cpp partitions this parent at 1,000 steps into 412,294 cycle leaves, 102,155 last-hole leaves, and 18,922 open leaves, with 23,190 split nodes. Completion mass: cycle 216,220,150; halt 22,052,705; total-defined 2,451,720; open 3,416,050. The initial maximum score is 804. Open roster SHA256: `4880fa9ce4eb0700ca53745e79b0e2b9186b466a55b406d57d9d6162ce1091b7`.

| Open-leaf classification | Number |
|---|---:|
| Reused finite automata (632-code bank) | 18,587 |
| Symbolic affine one-/two-block sweep seeds | 307 |
| N-gram closure | 6 |
| Block-FAR closure | 20 |
| Late first hole | 2 |
| Remaining discovery candidates | 0 |

The two late one-hole leaves encounter their holes at 1,288 and 1,095 ordinary transitions. No complete proof is claimed from simulation alone. The 307 affine seeds in growth.b64 reconstruct exact symbolic arbitrary-tail local equations using the existing sweep proof generator; the remaining automata are in special.txt. All 335 prior DFA misses have a witness proposal.

## Kernel audit

`Raw125Base.lean` sets up the first-hole split and parent coverage theorem. `generate.py` reconstructs the enumeration and builds audit shards with 26 explicitly retained residuals (six n-grams, twenty BlockFAR). `build_ngrams.py` and `build_blocks.py` generate independent original-source nonhalting certificates for those residuals. `Raw125ResidualClosure.lean` checks the exact residual table correspondence and closes the weighted parent once both independent source audits succeed.

The existing six-hole cut and residual workflows have a parent=125 input, preserving raw123 as the default. They are dispatched; no parent certificate or global residual count change is accepted yet.
