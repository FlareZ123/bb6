# Agent 2: four-seed root adapter for the shared D evaluator

One concrete consequence of the Critic's four-root direction is already available in Agent 3's source proof; please reuse rather than reconstruct it.

im-results/agent3-portfolio-raw-conjugacy/DAllStarts.lean and DExactTimes.lean give the all-six-start schedule:
- D0 start A → I9 after 36 raw steps;
- start B → I5 after 15;
- start C → I15 after 92;
- start D → I5 after 15;
- start E → I15 after 93;
- start F → I39 after 403.

The four October-16 rooted holdouts are therefore D0/I9, D3/I5, D2/I15, D1/I39 (state relabeling/reflection is separately source-certified). DExactTimes provides exact primitive-time iff statements, not merely eventual halting equivalence. The route evaluator need not be redesigned for four different tables: its unary seed parameter is the natural shared boundary.

A useful target is a theorem schema parameterized by n (or s : State) that turns a positive blockPartial terminal result at sect n [] into the corresponding raw HaltsCfg D0 (F0Pure n 0), then composes with every_blank_halts_iff_unary / DExactTimes. The current blankBlock_halt is reported only for blockPartial L 9 []; if its underlying blockPartial_sound and terminal extractor are already generic, this should be a small wrapper rather than a new proof of the block algorithm.

Semantic gate: CryptidBoundary freezes at state 6 after F/1, whereas BB6.Portfolio.D0 returns none at F/1. The sink state is reached one transition after the last successful live transition. ExternalTM62-D0-Bridge.md records the same convention; exact primitive halting-time statements must not inherit a +1 error. Also, the DAllStarts whole-tape root correspondence is in the Portfolio D0 semantics; any composition to CryptidBoundary still needs an explicit representation bridge (the I9-only bridge in RouteHalt may be reusable).

The exact seed/offset source is:
- DAllStarts.every_blank_reaches_unary, every_blank_halts_iff_unary;
- DExactTimes.all_blank_haltsAt_iff_unary, D3_haltsAt_iff_I5, D2_haltsAt_iff_I15, D1_haltsAt_iff_I39;
- DTableWitness.D{1,2,3}_halts_from_blank and exact-time conjugacies.

Please include this adapter question in the Route/ABE signature comparison. Do not assume the four roots have the same eventual outcome; they are four distinct seed questions.