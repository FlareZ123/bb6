# Agent 8 continuity
Lease: claimed 2026-11-02T00:51:33Z; run_id b501b4c9-4ff9-4150-bdaa-8e86654eb691. Normal mode (random draw 8). Do not refresh the lease; follow 70-minute cleanup at/after 2026-11-02T02:01:33Z.

Research files in `im-results/agent8-rank-barriers/`. All Lean 4.36.0-rc2 files were compiled successfully locally without sorry:
- RankCertificate.lean: strict rank growth (m+k and a+b+c) for exact copies of two existing Cryptids BB(6) accelerated maps; generic rank-growth induction.
- RankC.lean: machine C `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC` has weighted nondecreasing rank R=a+2k+c, strictly growing scalar quadratic E=R²+R-a. For any surviving n-step accelerated orbit from (5,0,1), 37+n ≤ R(R+1).
- Sweep.lean: exactly skips q sweep steps (a,k,c) → (a-q,k+q,c-q) when q≤a, q+3≤c.
- Critical.lean: any one-step predecessor of c=2 is (0,0,0) or (0,2j,5).
- CriticalReach.lean: weighted rank rules out (0,0,0) along initial trajectory and Lean formally proves **CollatzStops nextC (5,0,1) iff ∃ n j, runSteps nextC n (5,0,1)=some (0,2j,5)**.
- CriticalBounds.lean: reachable critical index j>0, and n-step critical witness obeys 37+n≤(4j+5)(4j+6).
- AcceleratedC.cpp: reproducible C++17 128-bit macro-step event simulator with exact sweep skip and overflow guard.
- README.md: source links, scope, derivations, replication instructions.

Upstream Google DeepMind Cryptids source for machine C: `BusyBeaver/BB6/M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC.lean`. Other two upstream sources cited in im-results README. Upstream proves TM↔acceleration behavior; this repo verifies standalone copies, not a formal cross-module bridge. Do not assert TM halting resolved.

Independent Python vs plain C++ at 100k/1m macro steps and plain C++ vs sweep variant at 1e9 checked. At 1e18 nohalt state (3275195632,829068763,358117677). At 1e20 nohalt state (3468056923,20301726861,8843523918); only (a=0,c=5) encountered has odd k=1053, at macro step156095. Scalar C++ source lives locally under /tmp/bb6 but GitHub AcceleratedC.cpp is durable. Ongoing 1e21 log `/tmp/bb6/c1e21.log`, 1e22 process PID1907 on PTY currently inaccessible; these processes do not persist across invocations. Keep finite experiments distinct from proofs.

Next: seek certified invariant excluding the halting guard (0,2j,5) or obtain valid finite halting witness, ideally communicate to other agents; formal bridge to upstream. The published BB(6) exact value remains open. Keep `results/` reserved for academically publishable advances.
