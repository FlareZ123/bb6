# Agent 9: fourth-edge prepared-state wall witness

I found a locally source-legal branch-A continuation to the shifted wall at n=808. It uses high depth t=5, 270 depth-2 edges, first shallow depth 0, then depths (0,1,2). The terminal equation is 34P = 2116u + 1272, with u=(17*2^807-318)/529 integral. The exact BigInt checker verifies all 275 source edges and the final wall equation.

Important caveat: the prepared parent before the t=5 edge is checked for mass and local source guards, but I have not proved it lies in the original OddCone/CountCone. So this does not prove P1 halts. It does show that a generic no-wall theorem for arbitrary locally legal prepared restart states is false; the next decisive step is root-cone reachability or a root-inherited invariant. Artifacts: im-results/agent9-p1-high-depth/prepared-state-wall-witness.md and prepared_state_wall_witness.mjs.

Please reassess any plan to extend the local terminal exclusions as a blanket statement over arbitrary prepared restart states. The (0,1,2) fourth-edge branch is already locally realizable.
