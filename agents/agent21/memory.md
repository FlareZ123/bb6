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

## Major new result at 05:18 UTC: genuine modulo32 infinite Machine C reset exclusion

Local Lean 4.36.0-rc2 kernel proved **for ALL naturals t**:

    BB6.CMod32.reset_mod32_sixteen_unreachable (t):
      ¬ BB6CLine.Reach (64*t+33,96*t+52,0).

This is reset index j=32t+16 in the PREVIOUSLY SURVIVING j mod8=0 class. A new nontrivial infinite family is now excluded beyond Agent11 prior modulo8 sieve. All actual Machine C/BB6 classifications remain open.

Proof is composed of two all-time forced predecessor lemmas:
    Reach(64t+33,96t+52,0) => Reach(160t+83,48t+25,0)
    Reach(160t+83,48t+25,0) => Reach(104t+52,76t+37,0)
Final target middle odd>=5, sum=180t+89 congruent1 mod4, contradicting our newly established universal CRange.reached_odd_zero_mod4_hole. No finite-step cutoff or hidden assumed unreachability.

The new generic backward precursor calculus (local CBack.lean) proves seven universal lemmas, including reached_kzero_odd, reached_high_pred, reverse_high, reached_zero_prev, reached_one_prev, reached_three_prev, reached_zero_hub, reached_hub_prev, reached_one_high_or_reset, reached_high_kzero_prev. Compiles without sorryAx. Local CMod32.lean compiles and #print axioms for first_ancestor, second_ancestor, reset_mod32_sixteen_unreachable shows ONLY [propext, Classical.choice, Quot.sound].

Sources saved in im-results/agent21-c-source-bridge/CBack.lean.xz.b64 (10,529 bytes, SHA256 84767aed6924f78e7aae1bc483a92f5aa068ccbb8f12fcfd888fa13777819474), CMod32.lean.xz.b64 (6,623 bytes, SHA256 52f852d6468489fe6bf5f1fb8963a8ed8ab49d6ea43a811862bf8787c1e9f086); im-results/agent21-c-source-bridge/reconstruct.py decompresses via stdlib and SHA-checks, atomic under filelock. CMod32Bridge.lean (plain) strengthens upstream original-machine halting equivalence by adding j%32 != 16. Manual CI workflow extended, two runs began 05:20:49 and 05:21:48 UTC; monitor and address failures. They take ~4min. Final theorem and hashes explained in MOD32-NEW-EXCLUSION.md. Broadcast sent 05:23Z, targeted prior requests to agent11 and agent10 at ~05:10Z.

LEASE AGE: Claimed 2026-11-02T04:18:37Z. 70min release threshold 2026-11-02T05:28:37Z. Be especially careful to checkpoint and release only after actual measured threshold. Before then continue checking CI and research. At threshold commit all useful state (memory/results) THEN DELETE LEASE AS LAST REPOSITORY MUTATION, verify deletion and end. User has been given partial final containing new result. GitHub sources already committed.


## External CI result (2026-11-02 05:27 UTC)

**Full pinned-upstream workflow SUCCESS:** https://github.com/FlareZ123/bb6/actions/runs/41393579178, job 125109990961. Sources restored under SHA256 check; Lean compiled CBack, CMod32, CMod32Bridge, original-machine Cryptids source, and Agent11's stronger modulo8 proof. The exact log reports:

    'BB6.CMod32.reset_mod32_sixteen_unreachable' depends on axioms: [propext, Classical.choice, Quot.sound]
    'BB6.CMod32Bridge.raw_halts_iff_mod32_gates' depends on axioms: [propext, Classical.choice, Quot.sound]

Thus the new infinite gateway exclusion and direct raw-TM halting equivalence, with added j%32 != 16, are independently verified. Later workflow run 41393881148 was queued after a trivial equality orientation edit and may be pending. Existing success already verifies all important theorems. Publishable result recorded in results/2026-11-02-machine-c-mod32-exclusion.md and index results/README.md.

LEASE release due when runtime system clock reaches 05:28:37Z. After any final memory checkpoint, check clock against .lease.json, then DELETE agents/agent21/.lease.json as FINAL repo mutation, verify remote deletion, exit. Do not research after lease removal.
