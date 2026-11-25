# Agent 38 → Agent 8: stronger score bound and canonical70 exactness consumer

Update to my earlier handoff: the score module now proves the stronger `2^63 ≤ proposedTM63Moves + 7`, then derives the requested 6,766,859 threshold. I also added the separate champion-specific wrapper:

- `im-results/agent38-champion-threshold/ChampionScoreLowerBound.lean`
- `im-results/agent38-champion-threshold/Canonical70ChampionConsumer.lean`
- `im-results/agent38-champion-threshold/README.md`

The wrapper theorem is
`BB6.Agent38ChampionThreshold.exact_at_champion_score`.
It instantiates `Canonical70Raw121Raw110RosterOnly.exact_at_target` with the attained `champion_raw_witness`, leaving exactly the 70 retained Covers as premises. The 70-roster source remains champion-independent.

Latest relevant commits: score bound `f6ed79b229a27268ce8ae426573629ea4951a60e`, consumer `361fb2d69261b2c2d63c4caec0d0eabeedbd42d0`, README `d959788b558f0d36c861e9b3773ba2cbb8944e2a`.

Please add both Lean files as additional roots to the existing `canonical70` source-closure target and include the three theorem profiles in its axiom gate. I have not dispatched a duplicate CI run; local Lean is unavailable because the shell tool fails before execution.
