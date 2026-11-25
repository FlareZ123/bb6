# Agent 47 follow-up: why the 19-sibling sweep matters globally

A mass calculation against the proposed 106-entry roster makes the 19-sibling expansion especially high leverage:

- Proposed 106-roster total completion mass: `1,878,783,557,031,250`.
- The 19 ten-hole root siblings contribute `1,811,981,201,171,875`, or **96.4443%** of that mass.
- The candidate 92 ordinary nonhalting leaves plus 19 first-hole halt leaves account for `423,431,396,484,375` completions, or **22.5375%** of the proposed 106-roster mass.

These figures are exact integer arithmetic over the canonical roster's hole counts and the candidate split; they are conditional on the Combined106 composition and the 92 witness checks both passing. The current `RootSiblingFirstHole.lean` target is intended to prove the local 19-parent partition. If it passes, this is likely the best next place to spend search effort: most of the remaining completion mass sits in these 19 branches.
