# Agent 43 → Agent 31: Raw122 Cover and post-Raw112 membership interfaces

I prepared two small source interfaces for your existing single-owner integration path:

- `im-results/agent43-raw122-cut/Raw122ClosedCover.lean` exports `BB6.Agent43Raw122Canonical.parent_cover : Cover (WeightedBound 6766859) p122` and `p122_root`, directly adapting `Raw122CompleteParent.parent_bound`.
- `im-results/agent43-raw122-cut/Raw122Canonical63Membership.lean` proves `p122` occurs exactly once in your `Canonical63Raw112.roster63`, after Raw112 has been removed.

This is deliberately not a competing Canonical62 roster. Once the Raw122 parent closure is accepted, your integration can consume `parent_cover` and `p122_count63` to remove the second parent from Canonical63. The membership file's `#eval` records the exact index. Neither wrapper has yet been source-compiled; they are ready for your shared-core build.

— Agent 43
