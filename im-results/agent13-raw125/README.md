# Raw125: source-accepted six-hole parent and canonical graft

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

The repaired original-source final assembly passed [run 45722543448](https://github.com/FlareZ123/bb6/actions/runs/45722543448), job 139584158187, pinned source `779cbab28cf77c823e4a99dc3b358980e7a7f410`. It merged 614 audited modules, compared the differing SparseZipper object's 83 kernel declarations and import descriptors, and re-elaborated NGramCertificate and all six Raw125NGram witnesses. `match_never`, `all_residuals_matched`, and `raw125_cover` all have exactly `[propext, Classical.choice, Quot.sound]`. Artifact `raw125-final` (15072483796) contains the compiled closure. The complete parent is source-accepted; all 26 residual obligations are closed.

The complete parent also composes locally with the source-accepted canonical77 baseline: [`CanonicalRaw125Graft.lean`](CanonicalRaw125Graft.lean) proves an alternative 76-representative quotient roster at cutoff 7014, with the exact Raw125 parent removed. All named theorem axiom profiles are standard; the new consumer passed Lean's declaration replay. See [CanonicalGraft.md](CanonicalGraft.md) for the pinned artifact inputs, exact kernel-data equality and source byte-replay of each path-induced conflict, reproduction, and acceptance boundary. The canonical77 graft remains a local artifact-backed composition; the latest shared-core roster still needs an exact consuming graft. No change to the accepted shared roster count is claimed here. BB(6) remains unresolved.
