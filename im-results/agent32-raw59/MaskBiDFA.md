# Sparse-map row-image certificates for Raw59

The new [MaskBiDFA.lean](MaskBiDFA.lean) uses sparse low-bit maps for both stack graphs and the relation rows, with masks of right summaries. For a nonempty row it checks that every set bit is listed. A right move checks the single left push, then unions the right predecessor masks separately for the two popped symbols and checks inclusion in the target row. A left move checks each right push edge and unions its images once, then checks inclusion in every left-pop target row. Missing map keys return no relation; no unchecked certificate data is trusted. The generic `never` theorem transfers perpetual zipper liveness to original `NeverHalts` for every compatible completion.

Lean 4.36.0-rc2 local original-source check used the accepted 0LE artifact 15054146521 (NGramCertificate and exact original imports). `image_sound`, `cell_sound`, and `never` print only standard axioms (propext, Quot.sound, Classical.choice where applicable). No native_decide or sorry.

## Same-witness comparison

Raw59/0LB/113, exact table `1RB0LB_1RC0LB_0RD0RF_1LD1RE_0RA1LA_---0LA`: a fixed 3,427-state exact-profile quotient with 137/209 stack classes. All variants use the same witnessed relation and edges, kernel row proofs, original source dependency objects, and a single sequential Lean process.

| Checker | Elapsed seconds | Peak RSS KiB |
|---|---:|---:|
| FastBiDFA array/trie | 39.79 | 2440600 |
| Array + listed bitset images | 30.22 | 2008332 |
| Sparse-map + listed bitset images | 4.43 | 1136308 |

The earlier 1,649-state folded witness is a distinct input, not the baseline of this comparison. An attempted mask enumeration using Nat.log2 was slower and abandoned.

[emit_mask.py](emit_mask.py) consumes the same independently saturated deterministic quotient record as the former emitter, preserves namespace/table/never interfaces, and verifies the candidate counts before emitting kernel-checked rows. [upgrade_data.py](upgrade_data.py) switches only the five pending branches (0LA, 0LB, 0LF, 1LB, 1LE) to this emitter and skips the expensive heuristic folding step. Their 128 exact/partner quotient candidates have 199,952 total abstract configurations versus 898,819 fixed-window configurations; the largest is 6,664 states. Earlier accepted 0LE/1LF generation remains unchanged.

This is a checker improvement and a route toward the pending Raw59 parent composition. It does not itself establish a parent Cover or reduce the accepted canonical roster. The full parent audit must still accept its entire partition, including non-n-gram leaves and the existing reused artifacts.
