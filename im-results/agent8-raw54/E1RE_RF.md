# Raw54 E1=0RE / 0RF (discovery checkpoint)
Both are six-hole cylinders below Raw54, not the older E0=1RF cylinder below E1=0LE.
Frozen enumeration and bank are the same as E1RC.

| E1 | split | cycle | last | open | frozen FAR hits | misses |
|---|---:|---:|---:|---:|---:|---:|
| 0RE | 21265 | 375448 | 101865 | 11783 | 11413 | 370 |
| 0RF | 33292 | 600718 | 145065 | 19934 | 19558 | 376 |

SHA256 of open.txt / miss.txt (newline terminated):
- RE: 900a840398ab32e0d28bc83993a9b3dc35d7d2a2ac1753346b34adc849b3ceac / 1f915928ae8b63032145f20f6459c66b9e27f959fafaafb66359024ecb5e9d7b
- RF: c059c8daa06660bbebc73c963239cf8067356e89ba978bc35c9a93cfda4be407 / 316ed5a98b5d635af42ef67651dd45e5bccaeb9bb151d6c22c64b9ff98cda28e

RE ledger: 181 FAR, 68 n-gram, 85 run-DFA, 31 affine sweep, 2 late first holes, 3 unresolved. RF ledger: 235 FAR, 84 n-gram, 38 run-DFA, 16 affine, 3 unresolved. All 47 affine proofs compiled locally against original semantics from the RF artifact, only standard axioms. FAR/n-gram/run candidates require kernel checking before Cover acceptance.
F lines specify FAR code then miss indices; N/R lines specify n-gram width or run-search parameters then indices; S lines specify index, state, left/right words, repeated word, increment, entry, affine cost coefficients (as in E1RC); H lines specify index, ordinary moves, zero-based hole; U lines list unresolved indices. RE late holes 206 (1240, F0), 285 (4075, F1). RF observed maximum 839 ordinary moves. These are candidates, not accepted upper bounds.
