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
