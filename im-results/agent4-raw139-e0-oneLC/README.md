# Raw139 E0=1LC: new six-hole cylinder investigation (Agent4)

The normalized Raw139 sibling E0=1LC is `[7,24,11,24,14,24,24,16,10,11,24,24]` under the existing code convention. This is independent of Agent6's zeroRC/oneRE/oneRF work. Earlier coordination incorrectly named 1RC (already covered by a cycle); the target here is 1LC.

## Discovery

The first new query is D0 at step 9. Full ordinary split tree: 26,256 split nodes, 603,889 leaves, comprising 376,456 cycle, 160,285 last-hole, 47,553 small FAR, 19,595 difficult leaves. All ordinary choices and the halt branch at each split must be accounted for in the eventual formal certificate. This cylinder contains 25^6=244,140,625 raw completions; that is a partition size, not a proven count of closed machines.

The difficult leaves: 19,261 block-FAR recipes, 52 translated-cycle recipes, 279 late queries, and 3 unresolved leaves (0-based indices). Three late queries are multi-hole, namely 8893/10211/15206; splitting the A1 query into all 24 ordinary choices gives 46 block-FAR, 12 cycle and 14 late first-hole descendants, no unresolved children. The immediate halt options are finite by their query times. Longest newly discovered late query: index 3158 at 204,884, F1 (bound candidate 204,890 after maximum blank delay and halt step). Maximum late child query 887.

Two novel drift witnesses were found by hashing the finite suffix at each new rightmost visited position, then checking the actual minimum position between matching events. For 13444 the entry/period/boundary is 3960/3037/2 and translation +81; for 13447 it is 3735/2079/29 and translation +87. These are infinite-run candidate certificates, not merely failure to halt within a cutoff.

## Open leaves

* 134: `[7,22,11,5,14,1,0,16,10,11,4,24]` (F1)
* 1661: `[7,5,11,19,14,1,20,16,10,11,6,24]` (F1)
* 15474: `[7,22,11,21,14,3,7,16,10,11,24,17]` (F0)

The first and last show structured sweeps, the middle grows a 110-block region. Need induction or a genuine invariant. No full cylinder Cover or global BB(6) bound is established. The reproducer is assembled from the same existing Agent6/48 algorithms and fixed per-index search scheduling; its individual search stages were executed locally, the consolidated file has not yet been run end-to-end. Discovery recipes must be translated to the repository's exact Lean checker before acceptance.

## Kernel-checked cycle Covers

`E0OneLCCycles.lean` verifies nine newly identified translated-cycle witnesses (12481, 12482, 12487, 12490, 13444, 13445, 13447, 18563, 18570) using the sound `zipCycle` checker. Local Lean 4.36.0-rc2 successfully compiled this module against CI artifact 15121390168's core. All nine `coverN` theorems are unconditional for every natural bound B, with axioms exactly `[propext, Classical.choice, Quot.sound]`. No native_decide. The first finite-window list checker exceeded memory; switching to the existing zipper checker resolved it. To reproduce, extract that artifact and use `LEAN_PATH=core lean -o E0OneLCCycles.olean E0OneLCCycles.lean`. These nine checked leaves are a subset of the discovery counts above, not an aggregate cylinder Cover.

## Closure of all three previously exceptional leaves (local kernel checks)

1661: exact sweep recurrence, state A, left stack 001 (head included), right stack (110)^(4n+17) 1111011 (110)^(4n+8) 111110111101. Blank entry at 2764; recurrence cost 1527+308n. Proof source E0OneLC1661.lean.gz, commit c0ee5cb272e31daa46f5e2379f04d0f2cb143a4c. Extract with gzip -dc; compile against accepted core 15121390168. The theorem BB6.Agent4E0OneLC1661.cover proves Cover at arbitrary B.

134: mirrored width-6 block-FAR, cap1/mod1/runs2, graph 26 left/135 right/321 edges; minimized 26 left and 76 right nodes. 15474: mirrored width-12 block-FAR, cap2/mod1/runs2, graph 494 left/3030 right/7149 edges; minimized 494 left and 455 right nodes. Both soundness modules and concrete invariant proofs compiled locally in Lean 4.36.0-rc2 against the same core, with [propext, Classical.choice, Quot.sound]. Width-specialization generator and exact data generation to follow in this dossier. No unresolved discovery leaf remains. Full 603,958-leaf compositional proof remains pending, and bound 204,890 is still candidate only.


## 2026-11-27 00:22Z: exact longest-query theorem and faster proof composition

All discovery cases are now classified (603,958 ordinary leaves), but the aggregate parent is **not yet certified**.

- The full first undefined query of leaf 3158, codes `[7,22,11,5,14,2,1,16,10,11,12,24]`, is exactly step index 204884 at F1.
- `OneLCFast.lean` proves the packed 60-bit transition-table interpreter agrees with the original binary zipper evaluator and hence the reference machine semantics.
- `OneLCSweep.lean` proves arbitrary-tail block sweep induction for packed tapes. `sweep_finite.py 3158 204884` (in a directory with the exact partition.json) produces 1621 actions: 607 sweeps, 14 rules, accounting for 163433 primitive transitions; 1014 finite fragments account for the remaining 41451 transitions. `emit_sweep3158.py WORK OUTPUT` generates the exact 51-chunk proof. All chunks, `OneLCSweep3158Merge`, and `OneLCSweep3158.cover` passed local Lean 4.36.0-rc2 kernel checks. The merge uses `OneLCJoinExact.lean` to transport an explicit equality of step counts instead of forcing reduction of the entire run.
- `OneLCSweep3158Tight.lean` passed the kernel: exact leaf weighted Cover at **204887**, proof that no smaller weighted bound works for this leaf, and an attained machine with `HaltsAfter m 204886` (204887 including halt). Exact possible blank delays are [0,1,2]. This is a local tight bound, not a BB(6) upper bound.
- `emit_sweep.py` generalizes independent chunks and emits a drop-in `OneLCLate{i}` adapter. For leaf 15429, 3 rules cover 71310 of 73323 primitive transitions. The generic proof is under testing.
- `OneLCPrefix.lean` is a kernel-checked extension of Agent48's `ZipPrefixAudit` to the hybrid block-FAR checker, equivalent to the original checked semantics.

Original full-parent workflow run [45914394333](https://github.com/FlareZ123/bb6/actions/runs/45914394333), exact source f05ea44fc3676f736db95279a2ee5c091960c618, successfully compiled the shared core and exceptional proofs and at least the roots 01,02,03,04,08,09,14. Root 08 covers 24013 ordinary leaves. Several large branch runners were terminated externally (exit 143), not Lean errors. The resumable workflow `agent4-raw139-e0-onelc-resume.yml` and `resume_root.py` save only atomically completed dependency-closed objects, using the same pinned source/core. First recovery run 45915693337 has produced root07 progress; subsequent passes can consume this exact artifact. No whole-parent or canonical-roster deletion claim has been made.
