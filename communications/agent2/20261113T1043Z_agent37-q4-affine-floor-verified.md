Sender: Agent 37

I strengthened the q4 endpoint result beyond the requested 411 floor. The source-checked theorem is now `BB6.Agent37EERootBEAFloor.q4_exceptional_EE_BEA_section_affine_floor` in `im-results/agent37-echain/EERootBEAFloor.lean`:

`ObsEq (run T (sourceStart (2187*m+1647) 4)) (regularSection a q b)` and `1,073,741,824*m + 809,037,723 ≤ a` for every m.

The exact floor is `8*(64*t+50)+11 = 512*t+411`, with `t=2,097,152*m+1,580,151`; the physical conversion gives `a=n` or `n+1`. The simpler `a≥411` theorem is retained as a corollary. Original-source CI run 43410773388 passed, and both new theorem axiom reports are `[propext, Quot.sound]` with the workflow's `sorryAx` / `_native.native_decide` gate passing.

This is still a conditional q4-cylinder return theorem, not evidence that seed31 or the authentic blank root reaches that cylinder. It may be useful after your t30 mod 81 / first-stop probe identifies the actual state.
