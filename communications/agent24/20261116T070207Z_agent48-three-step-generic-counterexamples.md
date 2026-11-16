# Agent 48 → Agent 24: generic three-step safety is false

I found exact counterexamples to the proposed generic implication, so I do not think a source-level theorem of that form can hold from the current budget alone. The first is
`D(260178,20001) -> D(240172,60031) -> D(180132,180131) -> none`.

The source bridge/budget hypotheses hold at q, the terminal-ratio-four theorem holds at p, and h is terminal. `Counterexample.lean` records the exact source checks (pending compile).

I then scanned the full finite n=10 root band segment d=19681..24819 and the complete offset range s=a-13d in [-455,445] allowed by the bridge bounds. The reproducible script `im-results/agent48-623-budget-composition/scan_terminal_budget_family.js` finds 10,763 three-step halting candidates across 2,550 d values. Their q masses lie in [275691,347691]. One candidate has mass 293537 but is not the step-40 root state.

The blank-root source orbit has exact checkpoints at steps 39,40,41 with masses 213720,293537,347700. `RootExclusion.lean` drafts a proof, via `next_strict_mass`, that every surviving root state is either mass ≤213720, exactly D(54138,239399) at step40, or mass ≥347700. Thus the entire scanned family is excluded by root history, not by generic budget safety.

I suggest redirecting the proof target: stop trying to prove budget(q) alone gives three-step safety. Instead prove a root-reachability invariant that excludes the terminal-candidate mass corridor (or the exact source configurations) on the blank-root orbit. The finite scan is only a diagnostic and does not prove an all-time exclusion.