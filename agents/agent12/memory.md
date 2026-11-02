# Agent 12 continuity, BB(6) research

## Identity and lease
- Normal mode selected by actual random draw 5.
- Claimed original run_id `bb6-agent12-20261102`, claimed_at `2026-11-02T02:22:23Z`. NEVER refresh lease. Check live UTC time against original timestamp **after every checkpoint**. Release only when age>=70 minutes (03:32:23 UTC): first commit all useful state, then delete `agents/agent12/.lease.json` as final repo mutation and verify.
- Repo `FlareZ123/bb6`, default branch main, private GitHub connector. Repo README prohibits per-commit CI.

## Most important results, all kernel checked Lean 4.36.0-rc2

Machine P1 `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`, standalone exact restatement of DeepMind's `G,T`, initial blank-entry accelerated hub `(2,1)`. Agent4 already formalized blank halting iff some critical `(2,14*2^n-2n-10)` reached. All theorems below are **about the acceleration**; direct original-TM certificate is separately available upstream. No full holdout decision or BB6 bounds claimed.

Source `im-results/agent12-backwards/InfiniteMod8Barrier.lean.xz.b64` (packed complete `NoFourthTarget.lean`; SHA256 of decompressed bytes `ea708a402104f1b333ba1e50cda8fe889ada6c01f1b5c4d997b4586d30d08501`; reconstruction instructions in companion README). This source proves:
- `blank_ne_fourth_critical`: `¬BlankReach 2 206`, n=4.
- `blank_no_four_mod_eight`: for ALL d>=28 with d%8=4, `¬BlankReach 2 d`.
- `blank_no_critical_one_mod_four`: for ALL n>=5 with n%4=1, `¬BlankReach 2 (14*2^n-2*n-10)`.
- Critical reusable `T_to_mult4_even`: every `T(a,c)=some(b,d)` with b%4=0, d positive even forces `b=2*a+6`, `c=d+a+5`; proof exhaustive even through recursive G.
- Standalone first result snapshot `im-results/agent12-backwards/NoFourthTarget.lean.xz.b64` contains n4 proof, less current.
- Theorems all compiled under local Lean, #print axioms standard `[propext, Classical.choice, Quot.sound]`, no sorryAx.

Second module `im-results/agent12-backwards/InfiniteMod16Barrier.lean` is **plain Lean**, imports reconstructed `NoFourthTarget`; proved and compiled:
- `blank_no_zero_mod_sixteen`: for ALL d>=64, d%16=0, `¬BlankReach 2 d`.
- `blank_no_critical_three_mod_eight`: for ALL n>=3, n%8=3, `¬BlankReach 2 H_n`, so n3 target (2,96) is forbidden.
- Same standard axiom audit. Full README and GitHub broadcast under `communications/broadcast/2026-11-02T0241Z_agent12-infinite-mod8-p1.md` explain and invite review.

## Main technique and next research
Complete backwards predecessor inversion for target (2,d):
(2,d) <- (d-1,0) <- (d-3,1) or (d-4,2). The (d-3,1) path forces positive even-a state (d-6,3), often excluded by reachable invariant `a=2∨a%4=0`. The (d-4,2) path is uniquely inverted via `T_to_mult4_even` to (z,z+7), then an odd-left predecessor (z-3,z+9), which violates the same invariant for d%8=4; d%16=0 requires one further G inversion before the contradiction.

Research next:
1. Try **d%16=8** barrier (critical n%8=7), then **d%8=6** (critical n%4=0) and **d%8=2** (critical n%4=2). Other agents' n0, n1, n2 statuses matter; n2 still unresolved gateway (36,3).
2. Integrate original upstream DeepMind TM-to-map semantics if decisive.
3. Preserve modular theorem tools, avoid duplicate elementary synthetic funnel work.
4. Exploratory Python complete inversion search indicated all targets n=0..285 close under forbidden-leaf backward search before 100k nodes; n286 hit node cap, no proof. Need preserve reproducible code if expanding. Source of `T` is in baseline Lean module.

Keep academically rigorous only in `results/`, supporting partial work `im-results/`.
