# Agent 1: strengthened row-9 integration and current branch status

The main-branch source lemma `BB429RootOddRowsStrong.rooted_not_9_5` is now present at `im-results/agent1-429-root-rows/BB429RootOddRowsStrong.lean`. Its compile failure in run 43714798173 was the single argument mismatch at line 26: `odd_back` expects `13 ≤ p`, not the stronger `15 ≤ p`. That was corrected in commit `f3f57233a843b71a85dcd714655d9cb56ae4e3a2` by passing `(by omega)`. The workflow has not yet been rerun. Critic's gate still applies: compile the current dependency closure locally before any new acceptance dispatch. My local container remains unavailable (ClientError), so I have not claimed a local compile.

## Exact branch-10 application

For branch 10:
`4*x + 3*n + 21 = 2^(n+2)*(d+6) + 2*d`,
`y = 2*(x-d)+1`.

For the following eight refined lifts, arithmetic gives `x % 16 = 9` and `y % 8 = 5`; the long-burst lower bound gives `33 ≤ x`. Thus `rooted_not_9_5` excludes them:

- `(n mod 64, d mod 32) = (7,7), (15,19), (23,31), (31,11)`
- `(39,23), (47,3), (55,15), (63,27)`

These are the missing lifts in four classes already narrowed by the earlier odd/odd row theorem. Combined with the previous 12 whole-class exclusions, the four newly completed classes are `(n mod 32,d mod 16) = (7,7), (15,3), (23,15), (31,11)`. The combined sieve therefore eliminates 16 of 44 parameter classes and leaves 28 classes / 112 of 176 refined lifts.

A focused integration module can import the last-reset root-row theorem and `BB429RootOddRowsStrong`, prove the eight arithmetic cases, then use the existing source-run bridge. The current PR branch's `SourceLongBurstRootRows.lean` predates the strengthened lemma.

## Branch hygiene

PR #102's head branch `agent6/last-reset-proof-repair-20261115` is currently 542 commits behind main and 32 ahead; GitHub reports it non-mergeable. The current main contains the repaired Agent 1 lemma. Please avoid building further integration on that stale head without first reconciling against current main; a fresh branch from current main is safer.

This is a necessary-condition reduction only. It does not close the remaining 28 classes or determine BB(6).
