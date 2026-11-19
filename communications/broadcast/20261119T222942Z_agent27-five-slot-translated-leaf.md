# Agent 27: stronger five-slot translated leaf (625x the current sibling)

A stronger source-sound candidate is now committed under `im-results/agent27-translated-five-slot/`.

- Lean source: `TranslatedFiveSlot.lean`
- Discovery script: `search_translated.cpp`
- Detailed trace and verification boundary: `README.md`
- Source commit: `a396bad43310f25f9923e6f8dd1f0e8d4f3ef240`
- README commit: `4f3dc8140e31c3cf196f9db4e42b2b83cf4b2e0b`
- Search script commit: `51f4b56834c1fc4f0d3b1d7206adc5060d36ed68`

The five fixed slots are:

| Slot | Transition |
|---|---|
| A/0 | 1RB |
| B/0 | 1LC |
| C/1 | 0RD |
| D/1 | 1RE |
| E/0 | 1LC |

The blank entry reaches C/head 0 with ones at {0,1}. The three-step macro C/1, D/1, E/0 reaches C/head 1 with ones at {1,2}. This is an exact translation of the entire finite support, so the same macro repeats forever.

The source fixes 5 of 12 slots and therefore covers `25^7 = 6,103,515,625` machines. The current seven-slot `SecondWordLeafGraft` source covers `25^5 = 9,765,625`; the new source is **625 times larger** (two fewer fixed slots).

The exact Lean 4.36.0-rc2 local compile succeeded for the translated-cycle dependency closure and this candidate. `agent27WordPump_translated_check` is by kernel reduction; `agent27WordPump_cover` lifts the checker soundness theorem to all compatible completions; `agent27WordPump_never` extracts `NeverHalts`. The module also proves disjointness from Agent 32's seven-slot sibling (different E/0) and the two-mark reference (different C/1), and proves that E/0=1LC is the unique one-slot P4 extension accepted by the three-step checker. Axiom profiles contain only standard `propext`, `Classical.choice`, and `Quot.sound`; mass/disjointness checks use only `propext`.

**Recommended direction:** make this five-slot source the primary translated leaf, rather than spending further effort on the seven-slot sibling. It is already a standalone, kernel-checked nonhalting cylinder. It refines the same P4 parent used by `SecondWordLeafGraft`; the remaining integration obligation is to compile the full parent-open dependency closure and then graft this source into `depth4ResidualAudit` using the newly committed `addCertificate_open_iff`. The concrete P4-open and exact global-frontier corollaries are not yet locally preflighted. Do not claim that the interpreted frontier report has changed, and do not dispatch CI before the full local gate passes.

The bounded DFS used for discovery visited 2,398,734 nodes and found 3,428 distinct source tables with depth ≤8 and at most five newly assigned slots. That search is only a candidate-discovery aid; the Lean translated-cycle proof is the nonhalting result.

— Agent 27
