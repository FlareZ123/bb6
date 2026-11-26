# q0 sibling-scan index 33: direct residual closure

**Status:** the isolated two-sided automata certificate and `Cover` leaf passed focused Lean 4.36.0-rc2 CI run [45789439603](https://github.com/FlareZ123/bb6/actions/runs/45789439603). The parent-level original-source Coq run [45789737554](https://github.com/FlareZ123/bb6/actions/runs/45789737554) was cancelled without parent acceptance. A proof-level sharded direct-source candidate is available. This is an intermediate local result, not a global q0 closure or a BB(6) upper bound.

## Exact post-decider residual

The existing q0 sibling scan reports one open leaf at active index 33:

`1RB1RD1RC0RE0LA---1LA1LD0LF0RB1LF0LC`

The sole unassigned transition is **C1**; the other eleven entries are fixed. This is the already-produced residual, not a new enumeration of the four-hole parent.

## Formal nonhalting certificate

The exact table already occurs as `R33L0` in `im-results/agent5-weighted-tnf-queue/Q0OpenAutomata.lean` and as key `R33L0` in `q0-open-automata.json`. Its table string is identical to the residual above.

`Q0Index33Automata.lean` isolates that one finite certificate instead of importing the full 94-leaf automata roster. It imports `TwoSidedAutomata`, checks the two finite stack relations and every represented transition (`checked`), and obtains `NeverHalts` through `BB6.Agent4Automata.never`. No bounded simulation or macro conjecture is a premise.

`Q0Index33MinimalHalt.lean` now proves:

- `residual_never`: every total machine compatible with this partial table is nonhalting;
- `residual_weighted_bound B` for every natural-number bound `B`;
- `residual_cover B : Cover (WeightedBound B) residual`, a genuine proof-carrying leaf covering the entire one-hole cylinder.

This is stronger than the earlier 25-to-1 minimal-slice reduction: the automata invariant proves that even the completion assigning **halt** to C1 never reaches that entry. Therefore all 25 completions are covered by one leaf at every weighted bound.

## What this does and does not close

The local residual cylinder is now covered mathematically: the focused Lean source closure compiled 15 modules and checked `residual_never`, `haltCompletion_never`, and `residual_cover`; the reported axioms are `propext`, `Classical.choice`, and `Quot.sound`, with workflow checks rejecting `sorryAx` and `native_decide`. The parent is q0 active index 33, exact table `1RB1RD_1RC0RE_0LA---_1LA1LD_---0RB_------`, four holes, `maxHalt = 156`, weighted bound 162. Its deterministic coarse/automata tree has 985 nodes, 41 first-hole splits, 55 MITM leaves, 140 terminal leaves, and one open leaf (R33L0). The original parent-level source run 45789737554 was cancelled. The new direct-source sharded candidate below is not yet accepted. This result does not close the entire q0 root family, the canonical64 roster, or BB(6).

## Independent computational observation

`verify_macro.py` remains a reproducible cross-check, not a proof premise. It replays the blank-run base case and 5,050 macro transitions for 1 ≤ j ≤ k ≤ 100 (1,455,800 simulated transitions). The observed checkpoints are:

- state F, head `H = 2k + 3 - 4j`;
- a singleton 1-marker at `-2k` and a contiguous 1-block on `[H, 2k+2]`;
- for j < k, the next checkpoint is reached in `8j+20` moves;
- for j = k, the next cycle checkpoint is reached in `4k+34` moves.

These observations motivated the original pilot but are no longer needed for the formal nonhalting result.

## Files

- `Q0Index33Automata.lean` — isolated `R33L0` two-sided automata certificate.
- `Q0Index33MinimalHalt.lean` — exact residual nonhalting theorem and weighted `Cover` leaf.
- `verify_macro.py` — independent deterministic simulation/replay only.

## Parent closure candidate: proof-level sharding

The exact 985-node first-hole tree (748 translated-cycle leaves, 55 coarse automata leaves, 140 terminal leaves, 41 splits, and one R33L0 automata leaf) has first split E0 at 27 live steps. Instead of original-source MITM saturation, the direct generator emits all 56 automata as explicit finite-stack certificates. The new [q0-direct-shards.cjs](../agent5-weighted-tnf-queue/q0-direct-shards.cjs) decomposes the same tree into 24 independently compilable first-split modules, two definition modules, and a final `Agent5Q0AutoData.v`. There are 162 independently evaluated subtrees (at most 25 nodes each) and 7 proof-level `source_first_hole_split` compositions. All 24 ordinary child transitions are retained at every split; the halt continuation costs at most n+6. The six nontrivial first-split branches are E0=1LB,1LC,0LF,0RF,1LF,1RF, with 121,121,169,145,289,121 nodes respectively. R33L0 lies within E0=0LF.

The generator was executed in the local JavaScript tool runtime on the existing checkpoint, scan and automata bank; it produced the 27 modules, 56 explicit certificates and exact single-open-leaf match before source checking. This verifies generation, not the Coq theorem. Use the existing manual `shared-rocq-root-proofs.yml` target `enumerate62-direct-parent`, offset 33. The workflow retains generated source and compiled shards even on cancellation. Acceptance requires `auto_parent_safe` and the exact q0 checkpoint consumer with assumption audits. No additional queue entry has been proved safe until the source parent check succeeds.


## Exact local maximum (independent finite certificate, not yet kernel-accepted)

The parent cylinder has maximum standard score **157** (156 live transitions plus halt query) and maximum weighted score **158**, where the weighted score adds the length of a zero-writing state path ending at A, capped at 5. The attaining table is

`1RB1RD_1RC0RE_0LA---_1LA1LD_0RF0RB_1LF0LC`.

It halts at C1 after 156 live moves, and C0=0LA gives the one-step zero-writing path C→A.

Proof by finite certificate: [check_exact_parent.cjs](check_exact_parent.cjs) rebuilds the deterministic first-hole tree and checks it with a separate absolute-coordinate tape simulator and explicit finite-stack closure checker. At a translated-cycle leaf the simulator verifies a positive period, displacement in the designated direction, no head excursion outside the protected half-line, and equality of the half-line tapes relative to the two endpoint heads. Translation induction repeats the period indefinitely; its entire trace uses assigned ordinary transitions. At each automata leaf, the two stack relations contain the blank seeds, every push is justified by a reverse pop edge, and every abstract control row has a defined transition and every permitted pop successor. Induction on concrete moves therefore proves no halt in any completion. Coarse certificates are reconstructed by full fixed-point sweeps rather than the generator's incremental waiter queues. Every first-hole node is replayed from blank with no earlier halt; it partitions the completion cylinder into its halt branch and all 24 ordinary transitions. Last-hole nodes have exactly one remaining hole, so their ordinary branches have no halt transition anywhere.

For a halt branch at live count n and slot h, form the possible zero-edge graph: assigned zero-writing state-zero rows supply their one edge, other assigned rows and h supply none, and other holes supply all six possible edges. A0 writes 1, hence no deterministic zero path ending at A can repeat a state (a repetition would trap it in a cycle). Every simple graph path ending at A can conversely be realized by fixing the distinct free rows it uses, without changing the replay to h. Thus the longest such path k is the exact attainable zero delay in that branch. The 181 halt branches have k=1 in 168 cases and k=2 in 13 cases. The maximum n+1+k is 158; the maximum n+1 is 157. There is exactly one halt branch for which the earlier generic n+6 bound exceeds 158: the attaining table above. This isolates the only place that needs a sharper delay argument to formalize the exact weighted maximum.

Reproduce: `node im-results/agent50-q0-index33/check_exact_parent.cjs` (run from repository root). The checked output is [exact-parent.json](exact-parent.json). All 985 nodes were evaluated in the local JavaScript runtime, including 748 translated-cycle certificates, 55 coarse finite-stack invariants, 1 explicit R33L0 invariant, and 181 first-hole traces. This gives a reproducible mathematical finite-certificate argument for the local maximum, not a new original-source Coq/Lean acceptance or a global BB(6) proof. The pending original-source sharded run is [45843560762](https://github.com/FlareZ123/bb6/actions/runs/45843560762), checking the conservative weighted bound 162 and the queue consumer; it is not a kernel check of the new sharp bound.


## Extension: all nine automata-residual parents

The same finite-certificate checker succeeds on all eight remaining parents in the 94-leaf automata bank, giving the following exact local maxima. Together with root33 this covers 22,977 tree nodes, including all 94 automata residuals (index28 is outside this bank).

| Active index | Tree nodes | Standard score | Weighted score |
|---:|---:|---:|---:|
| 26 | 361 | 195 | 196 |
| 33 | 985 | 157 | 158 |
| 34 | 1777 | 76 | 78 |
| 39 | 1873 | 139 | 141 |
| 44 | 2041 | 85 | 86 |
| 46 | 2017 | 59 | 60 |
| 48 | 3745 | 146 | 147 |
| 49 | 5785 | 229 | 230 |
| 51 | 4393 | 203 | 205 |

The maximum across their union is therefore 229 standard, 230 weighted. Each bound is attained by a concrete one-halt table. The other eight detailed outputs, including all attainers and the exceptional halt branches for sharper source checking, are in [exact-sibling-parents.json](exact-sibling-parents.json). Reproduce any row with `node im-results/agent50-q0-index33/check_exact_parent.cjs INDEX`. These are independently checked finite-certificate results in the executable mathematical model; they are not the original-source Coq roster acceptance. The checker does not infer safety merely from the searcher's termination or classification. It checks each cycle, finite-stack invariant, first-hole partition, and exact zero-delay argument independently.
