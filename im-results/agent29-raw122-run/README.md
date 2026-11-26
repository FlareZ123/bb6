# Raw122 run-aware residual certificates and packed late traces

## Scope

Target the exact Raw122 / canonical86 parent `1RB---_1RC---_0RD---_1LD1RE_---0LF_------` (E1=0LF). The pinned candidate-tree artifact is **15043765926** from run [45655656030](https://github.com/FlareZ123/bb6/actions/runs/45655656030), source 78e5a98ee00041bdeab2afdf747013a60bbe501f. The original Lean object closure is artifact **15012394320** from the earlier disjoint original-source audit. The already checked fourteen-child closure is retained in Agent43's dossier. The 118 distinct unresolved leaves extracted from the eight genuine residual branches in that generator snapshot are not an independently certified residual count for the full root.

## Nonhalting witnesses

[hits.tsv](hits.tsv) contains exact table, original shard, left/right DFA summary parameters and discovery-state count. [generate.py](generate.py) performs dynamic push/pop closure, quotienting by cross-context signatures, and independent finite-closure replay, then emits balanced, small-block kernel checks using the existing `IndexedBiDFA` proof. Old four-parameter summaries record bounded run lengths of the lag-XOR tape stream; extended summaries also retain a distal-end prefix, a modular word statistic, and runs of equal completed-run lengths. The generated Lean theorems establish **NeverHalts for every compatible completion** of the literal table.

Locally checked in Lean 4.36.0-rc2 against the original `BiDFA.lean`, `TreeBiDFA.lean`, `IndexedBiDFA.lean` source and retained core objects: M000–M101, with ordinary axioms only. (Extended M102 onward are in progress until individual kernel checks finish.) The first 100 witnesses reduce from 69,854 to 25,378 reachable abstract configurations after quotient. These are individual table results, not a new accepted parent residual count. A local exact graft of Raw122Kid23_06 also compiled. Agent43's prior 45702209290 already supplies seven checked 1LA/1RF planned shards; do not duplicate them.

[patch.py](patch.py) patches only exact unresolved literal tables, retaining every unmatched leaf and every original closed subtree. It also consumes Agent43's independently proved fixed-cost recurrent families. The existing targeted manual audit workflow invokes this patch. Candidate-complete branches need all original source checks plus a residual composition before being counted.

## Two exact late-hole traces

The following first-hole times and full-completion weighted upper bounds were locally kernel-checked with the original Raw122Base/SweepPumping/PartialAudit closure:

| Literal partial table | Shard | First query | Ordinary known steps | WeightedBound |
|---|---|---|---:|---:|
| `1RB---_1RC0RA_0RD0LF_1LD1RE_0RB0LF_1LC0LF` | 05_14 | A1 | 6,659,486 | 6,766,859 |
| `1RB0LA_1RC---_0RD0RB_1LD1RE_0LA0LF_1LB1LE` | 16_13 | B1 | 1,296,924 | 6,766,859 |

The weighted bounds use the original partial-audit last-leaf theorem, including blank delay and final halt step. Both `exact_run`, `last_check`, and `bound` theorems have only propext, Classical.choice, Quot.sound. No native reduction oracle is used. The first trace uses 78,359 actions / 307 kernel blocks (28 local motifs), the second uses 2,845 actions / 89 blocks (20 motifs). [PackedRun122.lean](PackedRun122.lean) proves equivalence to original zipper semantics; [PackedSweep122.lean](PackedSweep122.lean) lifts arbitrary-tail sweeps to packed words; [PackedAction122.lean](PackedAction122.lean) proves arithmetic repeated-word evaluation and compositional soundness. [late.py](late.py) deterministically reconstructs the source proofs from the exact tables. The source is checked by ordinary Lean reductions, with each local motif proved for arbitrary tails. The simulator is not trusted.

[Raw122ResidualCover.lean](Raw122ResidualCover.lean) proves the general composition theorem: a checked partial audit at B and independently bounded exact residual tables at C≥B imply the original parent weighted bound at C. This avoids recomputing the 7014 audit at the larger cutoff.

## Reproduce

Extract artifacts 15043765926 and 15012394320, compile the exact source closure with Lean 4.36.0-rc2. For the nonhalting proofs copy the three original checker sources from agent16-raw118 and agent1-bidfa-sat into the core work directory and compile in dependency order; run `python generate.py WORK [indices...]`, then compile the generated modules. For either late trace copy the three Packed*.lean sources to WORK; compile PackedRun122, PackedSweep122, PackedAction122. Run `python late.py WORK 0` or `python late.py WORK 1`; compile generated Base, Block*, Join*, PackedLate*, LateCheck* in dependency order. No source-level completion is inferred from Python output alone.

Current state: no new full parent or BB(6) upper-bound theorem yet. Final hard nonhalting leaves and branch-level source audit are the bottleneck.
