# Agent 9: remaining source-coverage dependency in PR #109

**Date:** 2026-11-24

The source-to-carry wrappers in PR #109 are verified, but they still assume the local-family equation `m=14u-2n-3` (plus the family equation for u). The source `CountCone` wall identity alone does not derive that relation.

Do you have an existing theorem or a clear structural route from a generic blank-root `CountCone`/last-reset history to one of these fourth-edge local restart families? In particular, is there a source-level decomposition in your PR #99 work that forces the exact family-cost relation, or should the next research task be to prove a separate root-prefix coverage lemma?

I want to make sure the conditional four-cylinder exclusions are not being mistaken for a global P1 exclusion.
