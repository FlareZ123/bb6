# Source-certified physical read-one branches and all-symbol traps

**Status (6 November 2026):** Original-source Lean 4.36.0-rc2 verification of **80 pairwise-disjoint nonhalting full-table cylinders**, a complementary **20 exact-three-step halting cylinders**, and a general finite-prefix all-symbol trap rule. Every partial table leaves nine of twelve transition rows completely unrestricted. All theorems compiled with only standard axioms in [manual CI 42306505800](https://github.com/FlareZ123/bb6/actions/runs/42306505800), which rebuilt the original Agent8 and Agent4 source modules. This is intermediate proof infrastructure; no historically difficult blank-root machine is decided, and BB(6) remains open.

## Mathematical outcome: a real marked-cell return

Take an arbitrary state `q` in B..F, an initial direction `d`, and an arbitrary zero-read write bit `u`. Fix two transitions:

1. `A/0 = (write 1, direction d, state q)`;
2. `q/0 = (write u, direction opposite d, state q)`.

The true blank-root run first writes a one at the origin and moves to the adjacent blank cell in state q; it then reverses to the origin. Its third physical input is precisely **q/1**, regardless of the value of `u`, because the origin still holds the marked one. The other nine table slots have no bearing on this three-event prefix.

Complete this genuine read-one input in either of the following two source-certified ways:

- **All-symbol trap:** choose any write bit `v` and either direction `e`, and fix `q/1 = (write v, direction e, state q)`. Both q/0 and q/1 now execute ordinary transitions back to q on every possible symbol, so all subsequent transitions are defined and the machine never halts. This yields `5 × 2 × 2 × 2 × 2 = 80` pairwise-disjoint nonhalting sparse cylinders.
- **Exact short halt:** fix `q/1 = halt`. The third attempted transition halts, so the **exact Busy Beaver step score is 3** in every full completion. This yields `5 × 2 × 2 = 20` pairwise-disjoint halting sparse cylinders.

The ten-way originally known A/0-zero-write turning-ray classes do not overlap either family. The new all-symbol trap also subsumes the **40** independently source-certified ray-turning cases where `e = opposite d`, documented in [MarkedReturnSource.lean](MarkedReturnSource.lean). The all-symbol argument additionally covers the `e=d` cases, where a fresh-ray proof need not apply because the head may revisit nonblank tape.

## Complete source-proof statements

[SymbolCompleteTrap.lean](SymbolCompleteTrap.lean) defines `BothSymbolClosed` and `PartialBothSymbolClosed`: every transition on both symbols from any state in a closed set is a nonhalting move to another state in that set. The original `run` semantics proves `bothSymbolPrefix_never` from a genuine finite prefix followed by a closed set. `bothSymbolPrefix_cover` lifts it to **all compatible full tables** when that prefix is checked on the original finite-support physical tape. `bothSymbolPrefixCheck_sound` and the reusable `bothSymbolFiniteOracle_sound` are fully proved Boolean source checkers for arbitrary state masks and bounded proof-search prefix lengths. The finite cutoff bounds **certificate discovery** only; the resulting statement is all-time nonhalting.

The same file defines `markedSinkTable`, proves `markedSinkParams_length = 80`, parameter `Nodup`, the source check `markedSinkParams_source`, and universal sparse certification `markedSink_source_cover`. The genuine original semantics is used, with no imaginary post-reversal read-zero simulation. `markedSink_unique` proves that a single complete table cannot extend distinct parameter tuples.

[MarkedHaltBranch.lean](MarkedHaltBranch.lean) provides the independent original-source physical halt proof. It proves `finiteHaltCheck_exact` for every accepted finite halt check; `markedHaltParams_check` verifies all 20 marked-cell trajectories by Lean kernel `decide`; `markedHalt_exact` proves `HaltsAfter m 2` for **every** compatible total machine; and `markedHalt_source_cover` constructs the corresponding `Cover (DecidedBelow 3)`. `markedHalt_unique` proves no two of the 20 families overlap, and `markedHalt_sink_disjoint` proves there is no full machine in both families.

[MarkedReturnSource.lean](MarkedReturnSource.lean), the first chronological proof, directly uses the original `finiteRayCheck_sound` after three genuine steps, providing a second independent nonhalting proof for its 40-case subfamily. Its `markedReturn_unique` and `markedReturnCases_mass` likewise prove disjointness and the per-cylinder mass.

## Raw-table mass and separation from prior classifications

Each sparse family fixes three of the 12 two-symbol control slots; thus each contains exactly `25^9` full tables. Both `markedSinkCases_mass` and `markedHaltCases_mass` are source-checked Lean theorems. Pairwise uniqueness and cross-family incompatibility yield the exact union:

| Outcome | Sparse cases | Fully specified tables | Full raw-space share |
| --- | ---: | ---: | ---: |
| Never halts | 80 | 305,175,781,250,000 | 0.512% |
| Exact step score 3 | 20 | 76,293,945,312,500 | 0.128% |
| **Combined** | **100** | **381,469,726,562,500** | **0.640%** |

The reference universe is the full raw `25^12 = 59,604,644,775,390,625` table set, before any state/symmetry quotient. The existing conservative first-event Z/D certificate family covers 52.786874368%; Agent32's ten reversing-ray classes, whose A/0 writes zero, add a disjoint 1.6%. Our 100 new cylinders all have A/0 write one and a reversing q/0, so they satisfy neither first-event Z/D condition. Therefore the **conservative analytic certified-or-decided union** increases from **54.386874368%** to **55.026874368%**, or exactly **32,798,572,998,046,875** raw complete tables. This is a simple disjoint combinatorial union of source-sound cylinder families, not a numerical evaluation of the adaptive Lean frontier.

The more comprehensive six-read-zero-row C++ census in [Agent32's dossier](../agent32-zero-prefix-global/README.md) reports 143,060,975 / 244,140,625 zero-row assignments classified, equivalent to 58.597775360% of raw tables. On the current 100 cylinder templates its independent classifier cannot reach a read-zero cycle, a physical short read-zero halt, or a pristine infinite outward ray: the marker at the origin prevents the reverse-direction ray check, and the physical scanner encounters the assigned read-one q/1 before its next zero-row action. Consequently these cases are outside that **specific C++ classified predicate** and, *conditional on its reported exact count*, add to **59.237775360%** (35,308,465,576,171,875 raw tables). An exact Lean theorem equating the C++ classified cardinality with the separate Lean `globalZeroRowAudit.report` has **not** been proved. This conditional comparative percentage is not promoted to a kernel-proved frontier mass.

## Reproducibility and limits

- [CI 42304709471](https://github.com/FlareZ123/bb6/actions/runs/42304709471) originally checked the forty authentic turning-ray cylinders.
- [CI 42306027519](https://github.com/FlareZ123/bb6/actions/runs/42306027519) verified the general all-symbol prefix invariant and 80 marked sink cylinders.
- [CI 42306505800](https://github.com/FlareZ123/bb6/actions/runs/42306505800) additionally checked the exact score-three siblings, their mass and pairwise disjointness. The final `#print axioms` output of all named theorems contains at most `[propext, Classical.choice, Quot.sound]`, with no `sorryAx` or mock imports.
- The selective manual workflow is [agent12-marked-return-source.yml](../../.github/workflows/agent12-marked-return-source.yml). No automatically triggered workflow was introduced.

**Authentic-root relevance check:** a deterministic examination of the 663 exact rooted RLE entries in [the October 16 holdout mirror](../../resources/BB6_holdouts_663_2026-10-16.txt) found **zero direct matches** to these 100 marked-return families and zero machines with any nonempty, globally closed all-symbol control-state subset (checking both symbols and iterating successor closure). This is an auxiliary finite file audit, not a Lean kernel theorem and not a decision about any holdout. No claim of resolving a difficult root is made.

**Next high-value direction:** compose the original `bothSymbolFiniteOracle` with the genuine physical read-one branch selection in [PhysicalTraceAudit.lean](../agent32-zero-prefix-global/PhysicalTraceAudit.lean), and seek a source-authenticated *difficult* rooted residual witness or another quantified invariant beyond finite control closure. More trivial raw-table mass alone will not prove the global upper bound or champion score.
