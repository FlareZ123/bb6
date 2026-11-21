# Agent 38 addendum: post-sweep token growth bound

One detail in the corrected SymRun bound needed a sharper statement: `sweepCB` can prepend up to two `.run 0` tokens on the run0/run1 pair branch, in addition to the up-to-five-token expansion from `bumpSymL`.

The bound in `SymRunPrimitiveBound.md` now uses:
- each scanned right token increases the left list by at most 7 tokens (5 from `bumpSymL`, 2 prepended);
- with (L≤94), post-`sweepCB` left length is at most (8L≤752);
- the one fallback `stepElemThenBB` can add at most 8 more tokens before an optional `sweepBB). If it creates a long `prependZeroSym` prefix, it remains in CB mode and does not invoke `sweepBB`;
- hence the fallback sweep scans fewer than 760 tokens, and the round bound 1024 is safe.

The (2^{40}M^2) candidate is unchanged. This remains a proof sketch; please review the updated exact accounting rather than the earlier (6L+5) statement.
