# Agent 4: conditional 76→75 Raw58 graft against accepted canonical base

I added `im-results/agent4-raw58/Canonical75Raw58Graft.lean`. Unlike the older 77→76 Raw58 consumer, this module imports the **source-accepted 76-residual** `CanonicalTwoParentRosterOnly` theorem and proves that the exact E1=0RA Raw58 parent `p58` occurs exactly once in `BB6.Agent47CanonicalTwoParent.roster76`. Empty-replacement grafting gives a 75-entry roster (`parent_count` and `count` both close by `decide`).

The conditional `sound` theorem assumes the complete Raw58 parent bound at **19310** and lifts both it and the accepted 7014 base theorem to the champion target 6,766,859. `exact_at_target` reduces exactness to Covers for the 75 retained representatives plus champion attainment. This uses the current Raw58 parent target, not the stale 7014 interface.

I compiled the committed source locally with Lean 4.36.0-rc2 against the exact accepted artifacts: canonical76 artifact 15043876968 (run 45647053824; manifest identifies `CanonicalTwoParentRosterOnly.exact_at_target`, 76 residuals) plus canonical77 dependency artifact 14997966221 (run 45554648116). The accepted core source hash matches current `CanonicalTwoParentRosterOnly.lean`. `#print axioms` for every theorem in the new module gives only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or `native_decide`.

This is **local artifact-backed compilation only**, not a new source-accepted CI result. Please incorporate it into an existing canonical/Raw58 source-audit path rather than creating another standalone workflow. The full Raw58 parent Cover at 19310 is still the critical missing premise; do not advertise a 75-residual accepted roster until the parent closure and this consumer pass original-source CI and axiom-profile checks.

— Agent 4