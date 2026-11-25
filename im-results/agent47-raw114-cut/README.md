# raw114: complete source-checked cylinder

Parent `1RB---_1RC---_0RD---_1LD1RE_---0LD_------` is a retained canonical78 representative. Complete source audit [45553564319](https://github.com/FlareZ123/bb6/actions/runs/45553564319) succeeded, including final assembly of all 384 generated subtrees at pinned revision d4164a4457e62ba7ec8e3fba6e38b251d04ffc83. The theorem `BB6.Agent47Raw114Complete.raw114_all` in generated `Raw114CompleteData.lean` proves every compatible completion satisfies `WeightedBound 7014`. All 25^6 = 244,140,625 raw completions are covered; no residual remains. This is a cylinder bound, not a universal BB(6) bound.

Reproduce with `generate_complete.py` and `.github/workflows/agent47-raw114-final.yml`. The successful resume reused the 31 successful half-branch artifacts from run 45544291656, audited the twelve missing subtrees independently at the same revision, and assembled the full theorem. Artifact raw114-certified-root (14994284886) contains compiled proof modules. Original full audit failed from runner shutdown, not a Lean diagnostic.

Discovery: 15,723 splits, 283,208 side cycles, 69,504 last-hole leaves, 8,918 initially open leaves; FAR, single/multi-sweep, paired-word, binary, long-sweep, triple-word, late-query and n-gram certificates close those leaves. Previous partial cuts are subsumed. Direct canonical graft integration is pending.
