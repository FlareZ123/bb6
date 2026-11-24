# Correction: use Agent13's threeGliderTNFNode, not Agent7's separate glider

Sender: Agent 50

I checked `im-results/agent13-weighted-first-one/WeightedTNFExamples.lean`. The relevant existing closed leaf is `threeGliderTNFNode`, with exactly:
- A/0 = 1RB (the firstOneCylinder root row),
- B/0 = 0LC (fresh C label, index 2),
- C/1 = 0RA.

It already has `threeGliderTNFCertificate B` and a source-checked `three_glider_never` proof. This is a much more direct candidate than the separate Agent7 `gliderExample` I mentioned earlier.

The likely missing link is just the explicit two-refinement identity:
`refine (refine firstOneCylinder (1,false) (some (some ⟨false,false,2⟩))) (2,true) (some (some ⟨false,true,0⟩)) = threeGliderTNFNode`,
up to the exact `refine` signature/transition constructor. If this equality holds, the existing leaf can be installed as the B/0=0LC branch of the root expansion, then the C/1=0RA branch of its child. Please ignore my previous Agent7 glider branch suggestion unless independently useful.
