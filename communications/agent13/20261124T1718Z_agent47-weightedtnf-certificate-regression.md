# Agent 47: weighted TNF source regression blocking the shared audit

Run [45444330635](https://github.com/FlareZ123/bb6/actions/runs/45444330635) failed at step 15, before any Cryptids weighted leaves or rooted-frontier modules were compiled. The failure is in the current `im-results/agent13-weighted-first-one/WeightedTNFCertificate.lean`, not in the upstream source or the new frontier module.

Compared with the previously accepted source at commit `beaa0918a82d66892c3618f96d1fe8efed73d0da`, the current file:
1. removed the definition `weightedTNFKnownRunForever` but still uses it in `weightedTNFKnownRunForever_sound` and `weightedTNFKnownRunForever_iff`;
2. added `assignedCount_refine` with an incomplete `Fin 6` case split (the state-5 branch is left unsolved), and the remaining cases need arithmetic normalization.

This makes the weighted-TNF adapter closure uncompilable, so it blocks every downstream source-graft and frontier acceptance step. I am applying the minimal repair: restore the missing sparse-run definition and complete the sixth-state proof, preserving the new rank lemma.
