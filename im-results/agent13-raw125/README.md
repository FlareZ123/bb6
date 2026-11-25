# Raw125: complete candidate classification of a six-hole parent

Parent: `1RB---_1RC---_0RD---_1LD1RE_---1RF_------` (canonical roster raw index 125). The first hole is F1 after 7 ordinary transitions. The target is a source-level `Cover (WeightedBound 1290)` for all 25^6 = 244,140,625 completions, not merely a list of observed nonhalters.

## Complete candidate search and accepted component audits

The exact cycle/first-hole enumerator from agent11-raw121/fast_enum.cpp partitions this parent at 1,000 steps into 412,294 cycle leaves, 102,155 last-hole leaves, and 18,922 open leaves, with 23,190 split nodes. Completion mass: cycle 216,220,150; halt 22,052,705; total-defined 2,451,720; open 3,416,050. The initial maximum score is 804. Open roster SHA256: `4880fa9ce4eb0700ca53745e79b0e2b9186b466a55b406d57d9d6162ce1091b7`.

| Open-leaf classification | Number |
|---|---:|
| Reused finite automata (632-code bank) | 18,587 |
| Symbolic affine one-/two-block sweep seeds | 307 |
| N-gram closure | 6 |
| Block-FAR closure | 20 |
| Late first hole | 2 |
| Remaining discovery candidates | 0 |

The two late one-hole leaves encounter their holes at 1,288 and 1,095 ordinary transitions. No complete proof is claimed from simulation alone. The 307 affine seeds in growth.b64 reconstruct exact symbolic arbitrary-tail local equations using the existing sweep proof generator; the remaining automata are in special.txt. All 335 prior DFA misses have a witness proposal.

## Kernel audit

`Raw125Base.lean` sets up the first-hole split and parent coverage theorem. `generate.py` reconstructs the enumeration and builds audit shards with 26 explicitly retained residuals (six n-grams, twenty BlockFAR). `build_ngrams.py` and `build_blocks.py` generate independent original-source nonhalting certificates for those residuals. `Raw125ResidualClosure.lean` checks the exact residual table correspondence and closes the weighted parent once both independent source audits succeed.

The entire cut passed [run 45606331500](https://github.com/FlareZ123/bb6/actions/runs/45606331500), artifact `raw125-cut` (15019117858). The 26 residual witnesses passed [run 45606194438](https://github.com/FlareZ123/bb6/actions/runs/45606194438), artifacts 15017493142, 15018056591, 15017473090, 15016809866.

The original final assembly [45609482655](https://github.com/FlareZ123/bb6/actions/runs/45609482655) failed. Reproducing the exact wrapper with the five downloaded artifacts and Lean 4.36.0-rc2 found the actual error: `matches` is reserved syntax. Renaming it to `certificateMatches` made the unconditional `BB6.Agent13Raw125.raw125_cover (B : Nat) (hB : 1290 ≤ B) : Cover (WeightedBound B) p125` compile. The closures contain 614 distinct modules. The identical-source `SparseZipper` object differs between the cut and ngram shard. Retaining the cut object, `NGramCertificate` and all six Raw125NGram witnesses were rebuilt against the selected imports, then the final wrapper recompiled successfully. The three wrapper axiom reports are exactly `[propext, Classical.choice, Quot.sound]`. No residual hypothesis remains.

The parent proof is locally accepted using the successful CI component artifacts; fresh remote assembly and canonical-roster graft are still needed. Run the existing residual workflow with `parent=125`, `cut_run=45606331500`, `residual_run=45606194438`. No global roster-count change or BB(6) exactness is claimed.
