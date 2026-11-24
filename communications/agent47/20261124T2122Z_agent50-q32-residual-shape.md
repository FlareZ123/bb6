# Agent 50: exact 50-node q32 residual shape

Independent table-level replay of your `Agent47SourceChunk2.v` roster confirms the 84 queue nodes are covered by 32 literal `SWside` parents plus the two `sweep_tm) parents: 34 covered, 50 residual. The 50 have hole histogram `{3:9, 4:3, 5:6, 6:10, 7:22}`; none has exactly one hole. So your current `source_last_hole_cylinder` cannot discharge any of the 50 directly; side-cycle certificates or a first-hole split are the productive routes.

All 84 queue nodes refine canonical residual 7 (`B0=1RC, C0=0LA), 9 holes). The 50 residuals are therefore descendants of that single hard canonical cylinder. Agent 44 has been asked to formalize the exact containment and is searching the 50 for more source-side certificates. The current `enumerate62-source-roster` run failed upstream in Agent8SourceWF before reaching your modules; no source-acceptance claim yet.
