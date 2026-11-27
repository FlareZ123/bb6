# Raw54 E1=0RE / 0RF — source-accepted exact thresholds
Both are six-hole cylinders below Raw54, not the older E0=1RF cylinder below E1=0LE.
Frozen enumeration and bank are the same as E1RC.

**Current status:** both complete Covers and exact thresholds passed original-source Lean 4.36.0-rc2 CI (RE 4076, RF 840). The exported theorems passed the standard-axiom audit. These are exact child-cylinder bounds, not a complete Raw54 or global-roster reduction.

| E1 | split | cycle | last | open | frozen FAR hits | misses |
|---|---:|---:|---:|---:|---:|---:|
| 0RE | 21265 | 375448 | 101865 | 11783 | 11413 | 370 |
| 0RF | 33292 | 600718 | 145065 | 19934 | 19558 | 376 |

SHA256 of open.txt / miss.txt (newline terminated):
- RE: 900a840398ab32e0d28bc83993a9b3dc35d7d2a2ac1753346b34adc849b3ceac / 1f915928ae8b63032145f20f6459c66b9e27f959fafaafb66359024ecb5e9d7b
- RF: c059c8daa06660bbebc73c963239cf8067356e89ba978bc35c9a93cfda4be407 / 316ed5a98b5d635af42ef67651dd45e5bccaeb9bb151d6c22c64b9ff98cda28e

RE ledger: 181 FAR, 68 n-gram, 85 run-DFA, 31 affine sweep, 2 late first holes, 3 original U entries. RF ledger: 235 FAR, 84 n-gram, 38 run-DFA, 16 affine, 3 original U entries. All 47 affine proofs compiled locally against original semantics from the RF artifact, only standard axioms. The complete FAR/n-gram/run certificates were included in the accepted aggregate audits.
F lines specify FAR code then miss indices; N/R lines specify n-gram width or run-search parameters then indices; S lines specify index, state, left/right words, repeated word, increment, entry, affine cost coefficients (as in E1RC); H lines specify index, ordinary moves, zero-based hole; U lines retain the six original discovery indices, now linked to exact source proofs. RE late holes 206 (1240, F0), 285 (4075, F1). RF observed maximum 839 ordinary moves. These late arrivals determine the accepted exact bounds.

## Exact nonhalting certificates
The original U entries are frozen discovery identifiers, not the current open-proof count. The first three new files below compiled locally with Lean 4.36.0-rc2 and the original SweepPumping dependency closure from accepted RF artifact 15143833177. Each never theorem quantifies over every compatible completion, and its axioms are only propext and Quot.sound.

- RE240: [Raw54E1REHard240.lean](Raw54E1REHard240.lean), commit 6860d486a31a1180339d5bebf005eb19b2dcf36f. Exact binary carry on arbitrary finite words, blocks P=1010, Z=0000, T=101. Entry 16. Carry P^n Z R -> Z^n P R costs 8n+16; overflow P^n T -> Z^(n+1) T costs 8n+24.
- RE356: [Raw54E1REHard356.lean](Raw54E1REHard356.lean), commit 967a07d5c558cd35b4215e1f3cd3a7ec974ed1de. A section with empty left and right 01(0101)^n00(10)^m0 1^k. Entry 65, (0,3,1). Transfer (n,m+1,k)->(n+1,m,k) in 12n+18; reset (n,0,k)->(0,2n+1,k+1) in 12n+21.
- RF85: [Raw54E1RFHard85.lean](Raw54E1RFHard85.lean), commit 4a34676487c25eb9de9da35d49574414c8cee291. Arbitrary finite radix-four word in blocks 0000,1011,0111,1111. Entry 10. Carry past n threes resets them and advances the next digit; costs 8n+26, 8n+24, 8n+22 for next digit 0,1,2; overflow cost 8n+26.

- RF47: [Raw54E1RFHard47.lean](Raw54E1RFHard47.lean) and its five dependency modules, commit 2210afc1c4ea2de4b1449e39aace5bcd27383636. Exact return macros on run-gap words; count quotient cls(n)=n for n<4, otherwise 4+(n-4)%7. Both stack abstractions use the first four run symbols, with suffix consistency encoded by 46 left and 395 right edges. Closure of 428 paired states was split into 54 kernel-decision blocks. The proof starts at blank after 20 transitions and proves positive progress from every represented configuration, avoiding F1. The checker uses only propext; the never theorem uses propext, Classical.choice and Quot.sound. [rf47_abstract.py](rf47_abstract.py) regenerates the finite invariant; it is not a trusted component. Kernel-checked module blob IDs 78991f5b01f4578d6946b32e9fe83305a3a28fd4 (Macro), 5351a1429eab17ffdc9c4becd55ea140dc01d6f4 (Runs), af29f83b1ea904f40314d71d7f3d053bd26f754e (Abstract), 85e039af20bd030baa6131fdd256227bd000a363 (Sound), fcc869b7ac584e0db3cf1a49a1988c89309d9d7c (Data), 6db8c6a55b66dddf06c219ccb1ebd4bb3a7c1c02 (Hard47).
- RE290: [Raw54E1REHard290.lean](Raw54E1REHard290.lean) (b7cd131319bc29f8c5bc201304c7827b1ba75632); prior source proof with entry 48 and epoch 12n+46. Included in the accepted source closure.
- RF359: [Raw54E1RFHard359.lean](Raw54E1RFHard359.lean) (213f96be4c66592ba29c5f323ff3a0d5f9fc82b4); prior source proof with transfer 16n+24 and reset 24n+55. Included in the accepted source closure.

## Exact attainable scores and aggregate audit

Original-source checked [RE witness](Raw54E1REBase.lean) has table 1RB0LD_1RC1RA_0RD0RC_1LD0LE_1LF0RE_1LB--- (F1 halt), 4075 ordinary moves, zero delay. Weighted score 4076. [RF witness](Raw54E1RFBase.lean) has table 1RB0LC_1RC---_0RD0RC_1LD0LE_1LF0RF_1RC1LA (B1 halt), 839 ordinary moves, zero delay. Weighted score 840. Both named Attainer.attained theorems compiled with only standard axioms; exact matching remote blob SHAs 512979b8d8424ac910fa1a83e82e910a26b60aa2 and f8ca60de7ad9b451c3e458b96ed0a9a445f9db00.

[generate_e1re_rf.py](generate_e1re_rf.py) (4356d9658ee30b726fb56f246ca55391f21b8e8d) deterministically reconstructs every candidate and sharp-bound audit using the frozen ledgers and base modules. Existing selective CI workflow extended at 8fb87edbcf37210cf4afde279f96995d1fc59624; RE and RF dispatches acknowledged: [RE run 45960006400](https://github.com/FlareZ123/bb6/actions/runs/45960006400) and [RF run 45960012324](https://github.com/FlareZ123/bb6/actions/runs/45960012324). Both runs succeeded; the exact original-source manifests and named theorem axiom gates passed. RE artifact [15183587278](https://github.com/FlareZ123/bb6/actions/runs/45960006400/artifacts/15183587278) (SHA-256 3ebe6132344a68528660dcf1621760a01aeebb47855c7cf68e9661adbe336b1f) contains `BB6.Agent8Raw54.E1RE.complete_cover` and `.exact_threshold`. RF artifact [15184007689](https://github.com/FlareZ123/bb6/actions/runs/45960012324/artifacts/15184007689) (SHA-256 75c68c5da91caaf04869413e6e223d4cc59ebec6978176522194c229cc06e52b) contains the corresponding E1RF theorems. The RE census's maximum early first-hole weighted score is 960; RF's is 840. RE's later first-hole row 285 controls the exact threshold.

