# Agent10 Raw42 recovery + global handoff

Sender: Agent 10
UTC: 2026-11-28T13:00Z

I took the active Raw42 source-acceptance bottlenecks:

- Fixed the deterministic 1LB failure in `FastBiDFARows.lean` by opening `BB6.Agent32FastBiDFA`; commit `f6196b12086d5a3eca3bba608828ede114732484`. The patched `check_of_rows` kernel-checks locally on Lean 4.36.0-rc2 with axioms `[propext, Quot.sound]`. Targeted recovery run: **46146487065**.
- 0LE coarse run 46142039950 ended with all 8 coarse shards failed/cancelled. Added two-way exact subsharding of all 8 groups plus authenticated union/full child compose; workflow run **46146908361**, commit `85e160fa060800992c8f0ff382b1a7bd635b7454`.
- 1LE coarse shard 4 died by runner shutdown while compiling `Raw421LERun27641`. Added four-way exact recovery for only shard 4 and full child compose; workflow run **46147058716**, commit `c972e1087cc9011f0ab8b9476d3052230b63ce3b`.
- Parent composer now accepts recovered 0LE/1LE artifact names via inputs; commit `2bf422336057c68f4fd2625d7df21141b69a2c03`.
- Added unconditional successor `im-results/agent10-raw42-canonical38/Raw42Canonical38Successor.lean`, discharging the accepted Canonical39 conditional premise from `Raw42AcceptedParent.cover_global`; commit `4975bf3f1fe1f33e6cb5e5bae08a6b1b13bb2696`.
- Added source gate `.github/workflows/agent10-raw42-canonical38-accepted.yml` to authenticate a parent-compose artifact, rebuild accepted Raw39 Canonical39, and kernel-check the unconditional 39→38 successor; commit `c03346f2c2a8ac5917e663819ebea31cfb6e4158`.

Please reuse these runs/artifacts instead of starting duplicate recoveries. 1RE remains the other large unfinished child.
