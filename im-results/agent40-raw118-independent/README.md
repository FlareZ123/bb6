# Raw118: source-accepted recurrent leaf certificates

Parent: `1RB---_1RC---_0RD---_1LD1RE_---0LE_------` (six holes, stable raw frontier index 118). This dossier records source-accepted nonhalting subfamilies and the current residual frontier; it does **not** establish a complete parent cover or a BB(6) upper bound.

## Original-source accepted certificates from this programme

All checks below used the existing manual `agent13-coverage.yml` workflow, Lean 4.36.0-rc2, the unpacked original source closure, and its fail-hard `sorryAx|native_decide` guard.

- **Independent counters — 10 exact tables**, zero-based indices 299, 320, 323, 325, 340, 345, 347, 348, 353, 363; [CI 45600114599](https://github.com/FlareZ123/bb6/actions/runs/45600114599). The section invariant is state F, empty left zipper, right zipper (0^{4+a}1^{1+b}) for independent naturals (a,b). Each blank run reaches the family after ten steps, and every family member has a positive-cost return. The two two-hole cases are 320 and 347; the other eight have one hole. The listed compatible completions total 1,450, conditional on the exact parent partition.
- **Finite phase graphs — 48 exact tables**, listed in [phase_candidates.tsv](phase_candidates.tsv); [CI 45601298658](https://github.com/FlareZ123/bb6/actions/runs/45601298658). Each proof uses a finite directed graph of repeated-word zipper families with positive-cost returns; generated search is not trusted by the Lean check.
- **Nested recursive counters — 14 exact tables**, six in [generate_recursive_counter.py](generate_recursive_counter.py) and eight in [generate_recursive_more.py](generate_recursive_more.py); [CI 45638645532](https://github.com/FlareZ123/bb6/actions/runs/45638645532). The two generated Lean modules were compiled together against the original source closure.

These three sets are pairwise disjoint and contribute **72 source-accepted rows** to the Raw118 hard set. The shared parent consumer independently checks the disjointness and containment assertions.

## Residual frontier and run-aware stack certificates

The 274-row hard set originally had 187 disjoint accepted leaves (105 symbolic pumps, 72 above, ten BiDFA/TreeBiDFA). The tree-bank proof for 2873 passed [45661562068](https://github.com/FlareZ123/bb6/actions/runs/45661562068). Eleven SAT proofs, including duplicate 2873, passed [45666893278](https://github.com/FlareZ123/bb6/actions/runs/45666893278). The 47 wide-window candidates are disjoint from these: 44 individual proof jobs succeeded in [45667306290](https://github.com/FlareZ123/bb6/actions/runs/45667306290); the three interrupted jobs (5180, 5187, 5368) are being repaired in [45672887654](https://github.com/FlareZ123/bb6/actions/runs/45672887654).

From the exact 87-row one-hole roster, subtract the 11 SAT and 47 wide candidate indices. This leaves 29 rows. Cross-combining 34 distinct known automata (33,524 pairs over the 29 rows) yielded a new certificate for 3970, table `1RB---_1RC0RA_0RD1RB_1LD1RE_1LF0LE_0RB0LE`, 47 abstract states and 25 stack edges. [Raw118SatCrossBank.lean](Raw118SatCrossBank.lean) passed original-source CI [45675206842](https://github.com/FlareZ123/bb6/actions/runs/45675206842).

### Run-aware abstraction

A stack summary reads from the distant end toward its head. For raw bit b, use either b itself or its XOR with the bit d positions earlier (initial history zero). Retain the last d raw bits for deterministic updates, the most recent transformed bit, and the lengths of the last k transformed runs. Each length is exact below c and periodic modulo p above it. Optionally identify distant all-zero padding with the empty stack. This captures unbounded periodic raw words by bounded transformed run summaries.

Discover the least reachable abstract configuration and stack-edge closure, including the implicit empty-stack blank edge. Fill unobserved DFA entries with zero and independently replay the ordinary two-sided DFA witness checker. The existing IndexedBiDFA theorem source-checks the explicit generated finite certificate; neither search nor compression is a trusted proof step.

Reproduce with `python run_summary.py` (or specific indices). The exact 87-row TSV SHA-256 is checked, as is disjointness from SAT, wide and cross-bank hits. The generator produces explicit left/right DFAs, Lean modules, and a manifest. Two source-check batches are pending:

| Batch | New indices | Original-source CI |
|---|---|---|
| Raw/lag-one runs | 1120, 1127, 1174, 1326, 1390, 1391, 1392, 1816, 2867, 3921, 4093, 4125, 4342, 4443 | [45675655736](https://github.com/FlareZ123/bb6/actions/runs/45675655736) |
| Trimmed and higher-lag runs | 430, 437, 440, 456, 1181, 3908 | [45676449188](https://github.com/FlareZ123/bb6/actions/runs/45676449188) |

If all pending certificates pass, eight hard rows remain: **10, 434, 655, 657, 2869, 3981, 4188, 4197**. These are candidate-level counts until the exact parent consumer compiles. The 20 run-aware certificates are not yet source-accepted.

## Parent closure boundary

The parent residual list has 959 rows: 679 sparse candidates, 274 hard rows and six delayed first-hole leaves. The prior consumer [45661985524](https://github.com/FlareZ123/bb6/actions/runs/45661985524) was cancelled; canonical membership [45639243857](https://github.com/FlareZ123/bb6/actions/runs/45639243857) ended in runner shutdown. Index 439's 756,495-step first-hole query has an accepted weighted certificate [45575655393](https://github.com/FlareZ123/bb6/actions/runs/45575655393).

The target is the **local Raw118 bound 756496**, not the much larger exact champion score C in [the attainment result](../../results/2026-11-24-champion-exact-attainment.md). On success, this would discharge one canonical cylinder by bound monotonicity. No parent cover, global upper bound or exact BB(6) value is claimed.
