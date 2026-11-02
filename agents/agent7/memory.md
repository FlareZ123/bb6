# Agent 7: P1 blank-reachability research

Normal mode draw 6 (actual secure RNG). Identity claimed `2026-11-02T02:15:36.839161Z`, run `3472182586ac3d1f87234c57`. Never refresh original claim timestamp. At every checkpoint measure actual clock. At >=70 min (after `2026-11-02T03:25:36.839161Z`) complete work, push, then delete lease as LAST repo mutation and verify.

## Verified first contribution (02:40 UTC)
- `im-results/agent7-rank-bounded/RankBase.lean`: universally proves fuelled structurally recursive `Gfast=G`, exact `Tfast=T`, rank monotonicity of `iterT`, and `no_target_bracket`: an exact one-step mass crossing from (2,1) excludes an arbitrary target for all finite times.
- `im-results/agent7-rank-bounded/RankCertificate.lean`: 192 checkpoints using kernel `decide`, exact first 1743 accelerated steps, nine all-time unreachable critical gateways `(2, H(n))` for n=0..8; `H(n)=14*2^n-2n-10`. The blanket theorem `no_first_nine` is fully formal, with `#print axioms` standard [propext, Quot.sound], no sorry. Prior Agent4 excluded first two via backward structural proof. This adds finite n=2..8 exclusions with a generalizable rank method. This is intermediate, does NOT solve the holdout or BB(6).
- `im-results/agent7-rank-bounded/generate.py` reconstructs certificates with an atomic locked write, input --max-target. README includes full data, limitations.
- GitHub Actions manual `.github/workflows/agent7-p1-brackets-lean.yml`, run https://github.com/FlareZ123/bb6/actions/runs/41378910646 **passed success**, verifying actual shared `Packet.lean` and `GParity.lean` with Lean 4.36.0-rc2.
- All commits on main; `results/` unchanged in respect of prompt (only genuinely publishable frontier work goes there).

## Potentially much stronger current research lead (NOT YET PROVED)
Developed complete inverse successor `predecessors(b,d)` for P1 accelerated map via finite inverse-G chain. Scratch `/tmp/agent7/back.py`, `back_pruned.py` (not committed yet); exhaustive tests first 100x100 small source states and 80x80 outputs. Reverse predecessor closure for critical H(n), n up to 285, found no starting (2,1) even when pruned by proven reachable even-left positive-counter modular invariant `a=2 or a%4=0`. This is empirical bounded data only; each fixed target has a finite backwards cone by strict mass increase.
In particular symbolic algebra suggests **all critical indices n≡1 mod4, n≥1** are globally excluded, using few backwards steps and Agent4's mod4 invariant. For H≡4 mod8 and H≥16:
(2,H) ← (H-1,0) ← (H-3,1) or (H-4,2).
(H-3,1) ← (H-6,3), which is even-left 2 mod4 and impossible from blank.
(H-4,2) ← (H/2-5,H/2+2) via unique direct G inverse (H/2 even), then ← (H/2-8,H/2+4), even-left 2 mod4 (since H≡4 mod8), also forbidden. Need formally verify predecessor completeness and all bounds, then Lean proof; no claim yet.
Potential n≡0 mod4 with n≥4 H≡6 mod8 similarly gives short backwards proof (two inverse-G branches). n≡3 mod4 likely has unbounded 2-adic-depth chain, and n≡2 mod4 more intricate.
This symbolic **infinite exclusion** is far more valuable than increasing finite brackets. Prioritize generalization and rigorous Lean proof. Coordinate with Agent4 and Agent6 to avoid overlap.

## Repo source and collaboration
- Main machine target: `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`; DeepMind upstream certified TM-to-map bridge only, not imported directly in standalone Lean.
- Agent4's `im-results/agent4-halting-funnel/BlankInvariants.lean` proves even-left reachable a=2 or a%4=0; other modules NoSecondTarget and ThirdTarget have exact predecessor structure; Agent6's GatewayBlank constrains odd-sector mod8.
- Critic broadcast warns to focus on truly blank-orbit questions and not duplicate synthetic family results.
- Local Lean installed at `/tmp/lean/lean-4.36.0-rc2-linux/bin/lean`.
