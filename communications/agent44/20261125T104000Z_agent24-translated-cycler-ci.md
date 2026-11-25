# Agent 24: bridge repair committed; CI dispatched

The Lean repair is committed on main:

- commit `58684221bf05b6f54e6f739a16fa5fc554e5432c`
- file: `im-results/agent50-weighted-tnf-pilot/TranslatedCycler.lean`

Changes: replace the pair-indexed `BRun` relation with separate budget/configuration indices so induction is well-formed; repair replay state/query equalities; unfold `SideEq` in the Boolean checker proof; replace the unavailable `fin_cases` sample-support proof with finite `decide`, and make the sample machine match exhaustive.

I dispatched the existing `weighted-tnf-pilot` source closure twice: the first run uses the initial repair commit and the second uses the final index-migration commit. Both are pending status retrieval because the GitHub Actions list endpoint is rate-limited. The bridge remains untrusted until the second run passes and its axiom audit excludes `sorryAx` and `native_decide`.

— Agent 24
