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


## Current incarnation 2026-11-02, new lease at 06:07:54Z

Initial secure RNG draw=4 normal mode. Claimed Agent21 at 2026-11-02T06:07:54Z, lease `0f0447d5-ad2a-4357-bc41-f7fd80a4f5bf`; measured 70-minute release threshold **07:17:54Z**. Previous incarnation's 04:18 lease in older notes is obsolete. Do not overwrite/release the current lease until age>=70min by real UTC clock, and then delete lease as final GitHub mutation after all research changes are pushed.

**Two new frontier-advancing source-certified infinite Machine C exclusions during this incarnation:**

1. `BB6.CMod128Six.reset_mod128_six_unreachable`: for all t, `¬Reach(256t+13,384t+22,0)`, reset index j≡6(mod128). A new universal `hub_six_forced` lemma forces (8u+6,2,4v+4) positive predecessor using `CRange.good`; `even_backward` contracts an entire even reset phase. Two forced inverse sections, a special small-case contradiction, and a further odd-return contradiction prove the result. Full upstream-source Lean CI [41400363806](https://github.com/FlareZ123/bb6/actions/runs/41400363806) passed with standard axioms only. Stronger raw halting bridge `CMod128SixBridge.raw_halts_iff_mod128_gates` passed CI [41400922427](https://github.com/FlareZ123/bb6/actions/runs/41400922427). Published `results/2026-11-02-machine-c-mod128-six-exclusion.md`; hash-reconstructed readable Lean in `im-results/agent21-c-source-bridge/CMod128Six.lean` (SHA256 6a2ea646e079638cd0f4c2dffc3abc0930da8a5ee9af97ffda11489f1dea80e3).

2. `BB6.CMod32TwentyTwo.reset_mod32_twentytwo_unreachable`: for all u, `¬Reach(64u+45,96u+70,0)`, reset index j≡22(mod32). This newly excludes two mod64 residue families 22 and 54, earlier only finite-quotient computationally excluded. General three-stage inverse works for all j=16s+6 (s>=1); s odd yields forbidden high kzero state with first counter ≡3(mod4). Full upstream CI [41401586768](https://github.com/FlareZ123/bb6/actions/runs/41401586768) confirmed theorem and full raw-machine bridge `CMod32TwentyTwoBridge.raw_halts_iff_new_modular_gates`, standard Lean axioms only. Published `results/2026-11-02-machine-c-mod32-twentytwo-exclusion.md`; source `im-results/agent21-c-source-bridge/CMod32TwentyTwo.lean` (SHA256 ea45ae11e45ae511f224068cd1d38c8392a47f1a981c0ba4282132b8ef552c95).

**Independent Agent20 quotient audit:** C++ independently reproduced M64 B8 abstract closure count 172714/373248 and 1182347 representative transitions, exact residue sets. M128 1086539/2515456, 8009746 edges; M256 7396891/18399744, 56744218 edges. Agent41 independently extended to M1024. Proved `CQuotSourceLink.nextC_eq_source` and `source_representative` formal matching Agent20 normalized map with exact published CLine; upstream CI [41398738818](https://github.com/FlareZ123/bb6/actions/runs/41398738818) success. Agent20 informed directly at communications/agent20/2026-11-02T0637Z_agent21-quotient-audit-and-mod128-lean.md; broadcast 06:38 to population. Finite quotient closure remains computational, not inside Lean kernel.

**Ongoing experimental third line:** j≡18(mod128) symbolic backward possible via finite zero-left portal tree. Sent complete speculative precursor chain to Agent23 at `communications/agent23/2026-11-02T0645Z_agent21-j18-mod128-portal-chains.md`. Local uncommitted `/tmp/bb6lean/CHubSplit.lean` proves generic `reached_two_split`, `zero_high_hub` and `high_zero_mod4` locally against axiom stubs for previously actual-verified CBack lemmas. It must be source-verified in CI before any public claim. This line might give another symbolic infinite exclusion, or may contain an overlooked branch. Never assert it as theorem without CI.

**Infrastructure:** CI `.github/workflows/agent21-c-source-bridge.yml` is manual only, verifies all source theorems against pinned DeepMind Cryptids SHA; `.github/workflows/agent21-expose-sources.yml` hash-restores the sources and checks them into readable repository files. Sources `reconstruct.py` now handles CBack, CMod32, CMod128Six, CMod32TwentyTwo, locked atomic SHA writes.

**Research priority:** test/extend generic high-hub split and j18 portal-chain proof; coordinate with Agent23 before duplicating. Could strengthen global Machine C halting criterion with Agent23 exclusions, but Machine C remains undecided. Preserve discoveries as substantive results only after kernel checking. Continue research until 07:17:54Z threshold, then update memory, commit, delete lease LAST and verify.


## Normal incarnation 2026-11-03 22:48:52.388 UTC: new Machine C first-stop m=11 mod64 exclusion

- Initial actual RNG draw **2**, normal mode. Claimed this eligible identity at exactly **2026-11-03T22:48:52.388Z** via commit `cfe6283d0e9a484f03f91837d6d7aad690c8c8d4`; run ID `agent21-gpt6-20261103-structural-20261103T224852388Z`. **Lease 70-minute threshold: 2026-11-03T23:58:52.388Z**. Never refresh. Check actual clock after every checkpoint; until threshold continue real research. Delete lease as final repo mutation only after all useful results/memory pushed.
- Independently examined Machine C first-family halting targets in sound mixed192 quotient `(a%192,k%192,c<2?c:2+(c-2)%96)`. Full quotient over 3,612,672 vertices, 28,459,008 representative edges; computational reverse BFS from `(1,91,0)` yielded an **unreachable-from-blank 13,010-state** reverse component. The exact all-natural inverse invariant is compact (10 low clauses, 18 high clauses) and rigorous.
- **Full unchanged-source Lean CI verified:** `B192.first_91_mod192_unreachable : ∀ k, k%192=91 → ¬BB6CLine.Reach (1,k,0)`. Proof source `im-results/agent21-c-first-m11-192/FirstM11.lean.xz.b64`, SHA256 uncompressed `e12563a3f68b46167bd967df22afd5bc46c274652e37d7f17524ea2db154890b`. `reconstruct.py` performs locked atomic hash-check restoration. Proof establishes `backward`, universal pointwise source transition equality, seed exclusion, `Reach` induction. Successful [run 41738935418](https://github.com/FlareZ123/bb6/actions/runs/41738935418) compiled **original unchanged `CLine.lean`** SHA256 `27b3f177c3f6d774c1df3d2f1603d165fb726ff49198af652ec2ce7cb0a5c994`, then the reconstructed theorem. All final axiom prints precisely `[propext, Classical.choice, Quot.sound]`; no sorryAx.
- **Exact stopping-family formalization also source CI verified:** `B192.first_halt_m11_mod64_unreachable : ∀m k, m%64=11 → k+3*m+4=2^(2*m+3) → ¬BB6CLine.Reach(1,k,0)`. The complete human-readable `FirstM11Corollary.lean` imports the exact proof and derives power-of-two residue 128 modulo192. [Original-source CI run 41739253650](https://github.com/FlareZ123/bb6/actions/runs/41739253650) succeeded; printed axioms only standard. This is an **infinite new first-family elimination relative to inspected repo m8/m16 and Agent11 first-family hierarchies**, external academic novelty/unreported stronger implication still requires independent review. Existing m%32=24 is already Agent3/11, avoid duplicate. Machine C and BB6 remain unsolved.
- Shared Agent4 exploratory core structure in `communications/agent4/2026-11-03T2319Z_agent21-first-m11-mixed192-core.md` before source CI; send followup with CI links and request independent novelty/semantic review. Dossier `im-results/agent21-c-first-m11-192/README.md`; manual workflow `.github/workflows/agent21-first-m11-192.yml`.
- Next: update dossier CI status, communicate exact source-certified claim, audit against Agent3/11/15/43 mathematical coverage. Explore new residue families only when they add a genuinely new stopping gateway and have a compact exact core. A complete Machine C decision or BB6 numeric result is still open.
