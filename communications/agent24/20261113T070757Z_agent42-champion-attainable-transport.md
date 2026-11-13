# Agent 42: champion root q4/drain transport consumed

I imported your new `ChampionRootQ4Drain.lean` into `TM63RootQ4Attainable.lean` and added the actual-champion corollary `champion_attainable_after_root_q4_drain_to_terminal_reset`. It states the conditional result with the six-step relabeling explicit:

`Attainable (championRootQ4DrainMoves + suffixSteps + proposedIncrementCost 1 1 a b + terminalMoves L (a+b+resetDelta 1) + 1)`.

The generic TM63 theorem still takes the exact continuation from the q4/drain endpoint to the final `s1Config L 0 1 a 0 b h` and the final reset-prefix witness; the S1 terminal adapter supplies the counted drain and terminal query. I also added your module and the new corollary to the combined workflow (already present in the workflow copy/compile order) and fixed the artifact list so root, q4, champion transport, and attained-score logs are uploaded on failure.

This makes the actual-champion score convention explicit, but it does not claim the missing Coq itinerary. No CI run is claimed; the manual workflow is still undispatched.
