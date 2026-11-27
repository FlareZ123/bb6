# Raw54 E1=0RE / 0RF (2026-11-27 07:15Z checkpoint)
Both are six-hole cylinders below Raw54, not the older E0=1RF cylinder below E1=0LE.
Frozen enumeration and bank are the same as E1RC.

| E1 | split | cycle | last | open | frozen FAR hits | misses |
|---|---:|---:|---:|---:|---:|---:|
| 0RE | 21265 | 375448 | 101865 | 11783 | 11413 | 370 |
| 0RF | 33292 | 600718 | 145065 | 19934 | 19558 | 376 |

SHA256 of open.txt / miss.txt (newline terminated):
- RE: 900a840398ab32e0d28bc83993a9b3dc35d7d2a2ac1753346b34adc849b3ceac / 1f915928ae8b63032145f20f6459c66b9e27f959fafaafb66359024ecb5e9d7b
- RF: c059c8daa06660bbebc73c963239cf8067356e89ba978bc35c9a93cfda4be407 / 316ed5a98b5d635af42ef67651dd45e5bccaeb9bb151d6c22c64b9ff98cda28e

RE ledger: 181 FAR, 68 n-gram, 85 run-DFA, 31 affine sweep, 2 late first holes, 3 original U entries. RF ledger: 235 FAR, 84 n-gram, 38 run-DFA, 16 affine, 3 original U entries. All 47 affine proofs compiled locally against original semantics from the RF artifact, only standard axioms. FAR/n-gram/run candidates require kernel checking before Cover acceptance.
F lines specify FAR code then miss indices; N/R lines specify n-gram width or run-search parameters then indices; S lines specify index, state, left/right words, repeated word, increment, entry, affine cost coefficients (as in E1RC); H lines specify index, ordinary moves, zero-based hole; U lines list unresolved indices. RE late holes 206 (1240, F0), 285 (4075, F1). RF observed maximum 839 ordinary moves. These are candidates, not accepted upper bounds.

## New exact nonhalting certificates
The original U entries are frozen discovery identifiers, not the current open-proof count. These three new files compiled locally with Lean 4.36.0-rc2 and the original SweepPumping dependency closure from accepted RF artifact 15143833177. Each never theorem quantifies over every compatible completion, and its axioms are only propext and Quot.sound.

- RE240: [Raw54E1REHard240.lean](Raw54E1REHard240.lean), commit 6860d486a31a1180339d5bebf005eb19b2dcf36f. Exact binary carry on arbitrary finite words, blocks P=1010, Z=0000, T=101. Entry 16. Carry P^n Z R -> Z^n P R costs 8n+16; overflow P^n T -> Z^(n+1) T costs 8n+24.
- RE356: [Raw54E1REHard356.lean](Raw54E1REHard356.lean), commit 967a07d5c558cd35b4215e1f3cd3a7ec974ed1de. A section with empty left and right 01(0101)^n00(10)^m0 1^k. Entry 65, (0,3,1). Transfer (n,m+1,k)->(n+1,m,k) in 12n+18; reset (n,0,k)->(0,2n+1,k+1) in 12n+21.
- RF85: [Raw54E1RFHard85.lean](Raw54E1RFHard85.lean), commit 4a34676487c25eb9de9da35d49574414c8cee291. Arbitrary finite radix-four word in blocks 0000,1011,0111,1111. Entry 10. Carry past n threes resets them and advances the next digit; costs 8n+26, 8n+24, 8n+22 for next digit 0,1,2; overflow cost 8n+26.

Previous incarnation left source files Raw54E1REHard290.lean (b7cd131319bc29f8c5bc201304c7827b1ba75632) and Raw54E1RFHard359.lean (213f96be4c66592ba29c5f323ff3a0d5f9fc82b4). Their compilation status has not yet been re-established in this incarnation. RF47 is still a mathematical holdout. No aggregate E1RE/RF Cover accepted.
