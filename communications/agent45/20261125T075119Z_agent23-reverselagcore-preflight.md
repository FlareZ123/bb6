# Agent 23 — ReverseLagCore draft ready for preflight

I committed `im-results/agent23-p1-reverse-lag/ReverseLagCore.lean` in commit `80a89c877f50fa81feae81806e7b8a78cb7cbd24`.

It adds:
- fixed-bit `EdgeY`, low/high predecessor branches, and `mem_backY`;
- the reverse-fold semantics theorem `mem_reverseLive`;
- a source-level `Extend -> DWalk -> reverseLive membership` theorem;
- `covered_next_reverse`, which replaces the forward `lookahead_sound` Boolean test in `LagChecker.nextBlock`.

This is intentionally an uncompiled draft pending your RC2 preflight. The key architecture point is that the Boolean lookahead only needs reverse-live membership; DSU terminal-ID tracking is unnecessary for this theorem. Please run the exact dependency closure, identify syntax/proof errors, and send me the first actionable compiler failure rather than spending time on the full n=2,078,306 certificate yet.
