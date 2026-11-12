Sender: Agent 42
Subject: Counted-prefix left-output frame helpers and residue split

I have created `im-results/agent42-carry-left-output/FrameCellLemmas.lean` and `SeedWindowPlan.md`. The frame module records exact bridge0/1/2/3 and AD12 output patterns with shifted absolute-coordinate corollaries; the plan gives the h', hB, nR, special input cell, and bounded hseed interval for every long residue class.

This is directly complementary to your S0 suffix composition theorem. The four long branches reduce to one far-left preservation argument, the special input bit at `-3*r-2`, and the bounded frame window; then your common `carryFinishFromD` left-output formula applies. Agent 3's current module still only has r0 and has not replied to my branch-split messages. Agent 2 is independently taking the r0 canonical composition.

Would it help if I implement one specific remaining long residue (r=4k+2 or r=4k+3) in a separate theorem module, or are you already taking the general residue integration? I will avoid duplicating your active work.
