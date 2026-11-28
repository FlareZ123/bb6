# Raw44 B1=0RC final ordinary C1 branches: witness and source-check status

This tranche adds new results only for C1=1LE and 1RE and their E/F siblings. The existing 20 source-certified C1 branches remain unchanged.

## Exact candidate partitions

Each representative fixes seven of twelve slots and has 25^5 = 9,765,625 physical completions. The deterministic search is `node discover.cjs '{"second":"1LE"}'` or `1RE`.

| C1 | Nodes | Splits | Last | Cycle | N-gram | Hard | Hard mass | Max live query | Candidate weighted bound |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1LE | 40,585 | 1,691 | 8,549 | 29,715 | 602 | 28 | 700 | 469 | 475 |
| 1RE | 42,193 | 1,758 | 6,722 | 33,298 | 402 | 13 | 1,525 | 149 | 155 |

The weighted bounds allow up to five prior blank moves and one halt query. The searches are untrusted and these are candidate parent bounds pending the complete cut check.

## New proven residual nonhalting lemmas

All 41 exceptional sparse tables now have actual local Lean 4.36.0-rc2 nonhalting theorems for **every compatible total completion**:

- 1LE: 23 AutoPump and five finite-automata-reduction (FAR) witnesses, all one-hole.
- 1RE: 11 AutoPump and two FAR witnesses, eleven one-hole and two two-hole.
- Seven FAR certificates have 3, 4, 4, 4, 6, 4, and 5 DFA states; the explicit DFA is saturated by `fastTryDfa` and checked by the original source theorem. Six use tape reflection.

The original compiled dependencies were recovered from accepted Actions artifact 15220979453 (run 46037817669, Raw13 closure). Exact source Git hashes checked locally against the current repository:
- Frontier.lean 115438c4f244b5416a91be4dd7a3f12103d5448d
- FastFAR.lean fd7f1fcd96f9d2befcad4298bd371ce7bb64c409
- Agent46AutoPump.lean 9fb5e24599f4037123dc87d4e722f400eccabf6b
- NGramCertificate.lean 186254e4dd3ea22faf7008fae4fcd090b3ab1208
- ZipThreeHoleAudit.lean af60c2d8032b4cc51ea71e933e2a9cacb145e745

New source/witness input hashes match the pushed blobs:
- Raw44RemainingFAR.lean a720d56ae34e33d72c99a70a9db2493dda36497b
- 1LE-autopump-certs.jsonl 83dafd59585c688a1eaea231dbc4d18a1742a2b4
- 1RE-autopump-certs.jsonl 12941f0b2e9cf3ee438ea1afcc1dd46cfe9aac0a
- original emit_autopump.py d1ec1361cb006fc0eb844bfca36dc8d1911f2b80

All seven FAR `never` axioms: propext, Classical.choice, Quot.sound. All 34 AutoPump `never` axioms: propext, Quot.sound. No sorryAx or native_decide.

## Reproduction and next mathematical edge

`python im-results/agent16-raw44/generate_remaining_c1.py /tmp/raw44-generated --branch 1LE` and `--branch 1RE` regenerate distinct module namespaces and exact 24-way child audits. The witness maps must match full literal tables; unexpected hard tables cause generation failure. Both generators completed locally. At this checkpoint the two full cut compilations are in progress; the already-checked residuals alone are not proof of the full parent. The remaining join is E/F weighted transport, the known halt at C1, and the 20 prior accepted C1 outcomes. No global canonical-count decrement or BB(6) value is claimed.
