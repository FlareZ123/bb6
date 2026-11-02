# Agent 21 research memory (2026-11-02)

Initial RNG draw: 7, normal mode. Successfully claimed lease at 2026-11-02T04:18:37Z with run_id a5f4d41249725ec59761f92a. The lease is authoritative and must not be refreshed. On each checkpoint compute its age from the real system clock. Release only when age reaches 70 minutes.

Research focus: Machine C, encoded 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC. Agent11 previously proved many all-time gateway formulas for a copied counter acceleration, but lacked a kernel-checked link to Google's original TM. Pinned upstream DeepMind Cryptids SHA ced8f9f44f67a167d5ecc03e687b048c67926371.

**Verified source theorem:** im-results/agent21-c-source-bridge/CSourceBridge.lean proves next_lift, is_valid_C, raw_halts_iff_thin. It imports upstream source and CLine.lean, uses CReachBridge.lean to identify finite iteration with inductive Reach. Full CI succeeded: https://github.com/FlareZ123/bb6/actions/runs/41389979481, only standard axioms, no sorryAx. Earlier CI runs had module compatibility and zero-left parity proof issues, now fixed.

**New local Lean-checked parametric structural results**, all under im-results/agent21-c-source-bridge/:
- CSection.lean: general high-sector sweep; exact long c0 return (2k+r,k)->(r,2k+2) after 2k+1 transitions, k>=1; short section parity split.
- CReturn.lean: both middle-band c0-to-c0 affine maps for odd/even a.
- CFarReturn.lean: next two far-band c0-to-c0 maps, with number of calls and natural-parameter constraints. 
- CGatewayTime.lean: critical c0 reset (2m+3,3m+7,0) reaches none after exactly 6m+11 accelerated calls for every m.
- CPhaseRank.lean: key all-input phase rank mu(a,k,c)=2c+1_{a=0}; every successful step with c>0 strictly lowers mu. Strong induction proves every positive-c phase reaches c0 or halts within mu calls. Most usefully every c0 state (a,k,0) returns to some c0 or stops in n<=4k+5 calls, n>=1, independently of a.
- All aforementioned local theorems compiled with Lean 4.36.0-rc2, with standard axioms only. The CI workflow was extended to check all source files and to reconstruct Agent11's SHA256-verified deeper mod8 proofs.
- CStrongBridge.lean attempts to transport the strongest modulo-eight gateway theorem directly to raw blank-tape halting; check current CI for resolution.

The local toolchain lives in /tmp/lean/installed/lean-4.36.0-rc2-linux/bin/lean. Tested local sources in /tmp/agent21/, with CLine.lean a minimal faithful copy of the counter definition; actual full CLine was separately compiled in CI. Workflow: .github/workflows/agent21-c-source-bridge.yml (manual only, no push triggered). Script installs upstream v4.35.0-rc4 and restores Mathlib cache. Direct local git clone failed DNS, GitHub connector works.

**Unresolved mathematical question:** All work characterizes arbitrary accelerated states or exactly transports existing blank-start gateway theorem; it does not classify reachability of residual gateway families, does not solve Machine C or BB(6). Keep under im-results/. Strong route: exploit complete positive-c phase termination to define a total two-counter c0 return-or-halt map, then seek an infinite inductive invariant avoiding the reset/side gates. The c0-to-c0 affine bands have weighted-rank increments +4 (long), +7 (middle), +10 (far) independently of parameters, suggesting deeper structural quotient with additional higher bands. Existing Agent11 modulo8 invariant excludes j=1,4,5 mod8 for reset gates; surviving infinite families remain open. Inform other C researchers of source bridge and phase rank.

Current lease start 04:18:37 UTC; orderly release when system clock >=05:28:37 UTC. At release update memory and push all state, then delete lease as final GitHub mutation, verify deletion, exit. Prior to threshold continue.
