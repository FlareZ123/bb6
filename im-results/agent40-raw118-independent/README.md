# Raw118: source-accepted recurrent leaf certificates

Parent: `1RB---_1RC---_0RD---_1LD1RE_---0LE_------` (six holes, stable raw frontier index 118). This dossier records source-accepted nonhalting subfamilies and the current residual frontier; it does **not** establish a complete parent cover or a BB(6) upper bound.

## Original-source accepted certificates from this programme

All checks below used the existing manual `agent13-coverage.yml` workflow, Lean 4.36.0-rc2, the unpacked original source closure, and its fail-hard `sorryAx|native_decide` guard.

- **Independent counters — 10 exact tables**, zero-based indices 299, 320, 323, 325, 340, 345, 347, 348, 353, 363; [CI 45600114599](https://github.com/FlareZ123/bb6/actions/runs/45600114599). The section invariant is state F, empty left zipper, right zipper (0^{4+a}1^{1+b}) for independent naturals (a,b). Each blank run reaches the family after ten steps, and every family member has a positive-cost return. The two two-hole cases are 320 and 347; the other eight have one hole. The listed compatible completions total 1,450, conditional on the exact parent partition.
- **Finite phase graphs — 48 exact tables**, listed in [phase_candidates.tsv](phase_candidates.tsv); [CI 45601298658](https://github.com/FlareZ123/bb6/actions/runs/45601298658). Each proof uses a finite directed graph of repeated-word zipper families with positive-cost returns; generated search is not trusted by the Lean check.
- **Nested recursive counters — 14 exact tables**, six in [generate_recursive_counter.py](generate_recursive_counter.py) and eight in [generate_recursive_more.py](generate_recursive_more.py); [CI 45638645532](https://github.com/FlareZ123/bb6/actions/runs/45638645532). The two generated Lean modules were compiled together against the original source closure.

These three sets are pairwise disjoint and contribute **72 source-accepted rows** to the Raw118 hard set. The shared parent consumer independently checks the disjointness and containment assertions.

## Additional two-sided tree-bank result

On 25 November, the existing tree-bank search cross-combined 49 distinct left/right automata pairs over the 87-row one-hole complement remaining after the prior 187 accepted hard-set rows. It found one additional exact table:

- **Index 2873:** `1RB---_1RC1LE_0RD0RF_1LD1RE_1LB0LE_1RA0RC`
- Pair: `L2874-R2874`; 436 abstract states and 61 stack edges.
- Lean theorem: `BB6Coverage.Agent16BiDFA.Raw118TreeBank.M2873.never`.
- Original-source closure and allowed-axiom check passed in [CI 45661562068](https://github.com/FlareZ123/bb6/actions/runs/45661562068); the theorem reports only `[propext, Quot.sound]`.

This is one more source-accepted nonhalting leaf. It reduces the pre-consumer hard-set complement from 87 to **86** one-hole rows. The generated theorem and manifest are preserved as the `raw118-treebank-generated` workflow artifact (artifact 15044129837); the deterministic search is in [search_tree_bank.py](../agent16-raw118/search_tree_bank.py).

## Exact boundary: leaf proofs are not parent closure

Before the new tree-bank hit, the 274-row hard set had 187 pairwise-disjoint accepted leaves: 105 symbolic pumps, the 72 rows above, and 10 original BiDFA/TreeBiDFA rows from [Agent16's Raw118 dossier](../agent16-raw118/README.md). With index 2873, 188 hard-set rows are source-accepted and 86 remain in that hard-set complement.

The larger parent-level residual list has 959 rows: 679 sparse n-gram candidates, 274 hard rows, and six delayed first-hole leaves. The sparse check [45642047107](https://github.com/FlareZ123/bb6/actions/runs/45642047107) was cancelled before acceptance. Index 439's 756,495-step first-hole query has its own accepted original-source weighted certificate [45575655393](https://github.com/FlareZ123/bb6/actions/runs/45575655393); the other five delayed leaves still need their packed source certificates. The canonical-membership/partial-audit run [45639243857](https://github.com/FlareZ123/bb6/actions/runs/45639243857) ended with runner shutdown (exit 143), not a Lean theorem diagnostic.

The full existing `weighted-tnf-raw118-consumer` target is now running as [CI 45661985524](https://github.com/FlareZ123/bb6/actions/runs/45661985524). It regenerates the sparse, symbolic, counter, phase, tree-bank and delayed-trace modules, then attempts the exact parent consumer and canonical-membership theorem. Until that run succeeds, the 86-row complement is a precise research frontier, **not** a source-checked parent residual theorem. Even a successful consumer will leave those 86 one-hole tables to be bounded at the champion score.

Do not promote these intermediate certificates to `results/`; no universal upper bound or exact BB(6) value follows yet.
