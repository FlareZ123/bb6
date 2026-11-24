# Finite-automata reduction for the authentic sparse six-state frontier

Agent 7, 2026-11-24. Intermediate source integration; no BB(6) decision.

A standard one-sided finite-automata reduction (FAR) certificate is now
formalized directly over the repository's raw two-way infinite tape and
partial-table semantics. An unassigned row is treated as a failure,
so any accepted certificate proves nonhalting for every compatible total
completion. The proof does not use the search cutoff or trust the
saturation implementation. A left DFA reads the finite left word from
the far blank end; an NFA reads the head/right word. Its bad-language
set at the infinite zero suffix is checked as a fixed point. Closure
under both move directions is verified explicitly.

FAR.lean, FARCheck.lean, FARSearch.lean and FARBi.lean passed local Lean
4.36.0-rc2 against a slice of the exact Frontier and Symmetry interfaces,
with standard axioms only. FARExample.lean uses a concrete kernel-decided
certificate. FARFrontier.lean adds the checked oracle only to unresolved
leaves of the existing depth-four physical lasso audit; the old branches
and old certified leaves are unchanged. The exhaustive and mass
conservation statements are independent of the certificate generator.
The core FAR/Frontier closure passed original-source Lean 4.36.0-rc2 CI in [run 45342809760](https://github.com/FlareZ123/bb6/actions/runs/45342809760). The later bitset-optimized `FastFAR` checker and `FastCanonical` integration passed the current source closure, with a depth-one canonical report, in [run 45383596624](https://github.com/FlareZ123/bb6/actions/runs/45383596624). The `WeightedTNFBridge.lean` adapter, which turns `fastOracle_sound` into the existing weighted-TNF nonhalting leaf, also passed the combined original-source closure in [run 45384542491](https://github.com/FlareZ123/bb6/actions/runs/45384542491). The specific depth-four `FARFrontierReport` count is not recorded here; the numerical figures below remain computational predictions, not a kernel theorem.

## Hard-root search update (24 November 2026)

The pinned [663-machine holdout roster](../../resources/BB6_holdouts_663_2026-10-16.txt) was searched again by the existing untrusted C++ generator. [Run 45383617366](https://github.com/FlareZ123/bb6/actions/runs/45383617366) completed all eight shards with exact enumeration of canonical five-state DFAs and 30,000 guided mutation trials per DFA size 6–10, in both tape orientations, for every roster entry. No candidate certificate was emitted. The #746 table is included at roster line 618.

This is a bounded heuristic search result only. It does not prove that a certificate of these sizes is impossible, does not rule out larger automata or other invariant classes, and gives no verdict on any machine. Do not spend further compute merely increasing the same random-mutation budget; a materially different synthesis method or a deeper TNF-leaf application is needed.

A separate canonical enumeration predicts the exact old baseline
40,570,831,298,828,125 (68.06656%) and 2,011,108,398,437,500 additional
nonhalting completions (3.37408 percentage points; 160 three-row and
9,180 four-row raw cylinders). These are computational predictions until
the original proof-carrying frontier report is evaluated. No claim that
the remaining hard-root roster is decided; small DFA sizes 1–4 gave no
hits on the historical 663 roster.


## Depth-eight FAR cross-check and the actual 101-leaf frontier (24 Nov 2026)

The exporter `extract_depth_eight_residuals.js` reconstructs the checked `Tree.residuals` from `root-frontier.json` and `DepthEightSiblingData1–4.lean`. It reproduces 107 unique open leaves: 101 one-hole and six two-hole. The six two-hole tables are exactly the six existing growth-witness tables, not six new frontier reductions:

| Parent/tree | A/1 child | DFA | FAR run |
|---|---|---:|---|
| 86 / tree86 | `0LB` | 5 | [45466300325](https://github.com/FlareZ123/bb6/actions/runs/45466300325) |
| 86 / tree86 | `1LD` | 5 | [45466309502](https://github.com/FlareZ123/bb6/actions/runs/45466309502) |
| 112 / tree112 | `1LC` | 4 | [45466318520](https://github.com/FlareZ123/bb6/actions/runs/45466318520) |
| 112 / tree112 | `1RD` | 4 | [45466327492](https://github.com/FlareZ123/bb6/actions/runs/45466327492) |
| 112 / tree112 | `1LE` | 6 | [45466336469](https://github.com/FlareZ123/bb6/actions/runs/45466336469) |
| 112 / tree112 | `1LF` | 4 | [45466346380](https://github.com/FlareZ123/bb6/actions/runs/45466346380) |

The overlap is exact: the two `0LB/1LD` tables are `Agent50TripleSweep.table false/true`; the four `1LC/1RD/1LE/1LF` tables are `Agent50OnesSweep.table 0..3`. Thus `siblingFinalRoster_count = 101` remains the actual unresolved frontier. `DepthEightFAR.lean` preserves independent FAR `Data` objects and `WeightedTNFCertificate B p 6` adapters for all six growth-covered tables; [regression run 45469255283](https://github.com/FlareZ123/bb6/actions/runs/45469255283) compiles the archived module and exporter successfully. These are alternate proofs, not a reason to change the existing tree.

### One-hole residuals

The 101 genuinely unresolved tables have their unique hole at F/0 (50), E/0 (24), or A/1 (27). A bounded blank-tape simulation of each table for 1,000,000 steps found:
- 101/101 reached the step cap without querying the missing row;
- 0 reached an assigned halt;
- maximum absolute head displacement: 1,485;
- maximum nonblank-cell count: 1,244.

This is empirical evidence only: it does not prove the hole is never reached after the cap. Reproduce the roster and the bounded experiment with:

```sh
node im-results/agent7-far/extract_depth_eight_residuals.js --one-hole --simulate-steps=1000000
```

Four representative one-hole targets have now produced universal FAR nonhalting certificates. Each generated `hard1` theorem was accepted by Lean with only `propext`, `Classical.choice`, and `Quot.sound`:

| Parent/tree | Exact one-hole table | DFA/orientation | Run |
|---|---|---|---|
| 85 / tree85 | `1RB0LD_1RC1LF_0RD1LA_1LD1RE_1RD0LB_---0LA` | 4 / original | [45469713882](https://github.com/FlareZ123/bb6/actions/runs/45469713882) |
| 114 / tree114 | `1RB---_1RC1LF_0RD0RC_1LD1RE_0LB0LB_0RC0LA` | 1 / reflected | [45469722441](https://github.com/FlareZ123/bb6/actions/runs/45469722441) |
| 116 / tree116 | `1RB1LA_1RC1LF_0RD1RC_1LD1RE_0LA0LB_---0LA` | 6 / original | [45469732966](https://github.com/FlareZ123/bb6/actions/runs/45469732966) |
| 128 / tree128 | `1RB0LB_1RC1LF_0RD1RF_1LD1RE_---0LB_1RB0LA` | 5 / original | [45469741496](https://github.com/FlareZ123/bb6/actions/runs/45469741496) |

The corresponding weighted TNF leaves are `p85_0_leaf`, `p114_0_leaf`, `p116_0_leaf`, and `p128_0_leaf` in `DepthEightFAR.lean`. [Regression run 45470400658](https://github.com/FlareZ123/bb6/actions/runs/45470400658) compiles these four plus the six growth-covered alternatives and the residual exporter, rejecting `sorryAx` and `native_decide`.

Exact paths to the open leaves, using `moveIndex = 4*next + 2*write + right`, are:
- `DepthEightSiblingData1.lean`, `tree85`: A/1=`0LD` (12), then E/0=`1RD` (15).
- `DepthEightSiblingData1.lean`, `tree114`: E/0=`0LB` (4), then F/0=`0RC` (9).
- `DepthEightSiblingData2.lean`, `tree116`: E/0=`0LA` (0), then A/1=`1LA` (2).
- `DepthEightSiblingData4.lean`, `tree128`: F/0=`1RB` (7), then A/1=`0LB` (4).

These four are genuine members of the 101-entry `siblingFinalRoster`, unlike the six growth-covered two-hole tables. The proof objects therefore close four of the 101 unresolved leaves; the shared `siblingFinalRoster_count` remains 101 until Agent 50 integrates these paths into the tree. After that integration, 97 one-hole leaves will remain.

## Canonical-search to weighted-TNF bridge

`CanonicalTNFBridge.lean` now imports the existing canonical audit/search stack into the weighted first-one certificate interface.

The crucial bound conversion is:

[
\operatorname{DecidedBelow}(B-5)(M)
\quad\Longrightarrow\quad
\operatorname{WeightedBound}(B)(M),
]

provided the partial table has the authentic first-one root `A/0 = 1RB). The proof uses `firstOne_terminal` to establish that state 0 is a terminal node of the zero-writing graph, then `delays_subset_possible` to place every weighted delay in `possibleDelays p 0`. That list is filtered from `List.range 6`, so every delay is at most five. Halting-time uniqueness identifies the primitive halting index in the canonical decision with the index used by the weighted bound. The five-step margin is therefore a proved six-state graph bound, not a heuristic allowance.

The exported interfaces are:

- `decidedBelow_to_weightedBound`: converts one machine's primitive decision at (B-5) into its weighted bound at (B).
- `canonicalAudit_to_weightedCover`: converts a closed `Canonical.Audit` (the unresolved report component is zero) into `Cover (WeightedBound B) p`.
- `canonicalAuditTNFLeaf`: packages that cover as a `WeightedTNFCertificate`.
- `canonicalSearchTNFLeaf`: wraps the existing `Canonical.search` directly. It takes the same ray/scan/lasso/entry/macro/FAR limits and depth, runs the canonical search at (B-5), and consumes a proof that its unresolved report is zero. `Canonical.Scoped` is explicitly translated to the slightly stronger-shaped `TNFSupport` predicate.

This is the useful integration point: the canonical search already combines physical-trace, lasso, entry-macro, and FAR leaf oracles. A closed result can now become a weighted-TNF leaf without implementing a second copy of those search methods. It does not make an incomplete audit complete; the required `report.2 = 0` proof remains the exact closure obligation.

`CanonicalTNFExample.lean` exercises the conversion on the four-row glider: it turns the explicit FAR certificate into a certified canonical audit, then into a weighted-TNF leaf, and proves `WeightedBound B` for every (B\ge5). The direct FAR-to-TNF example and its soundness theorem are in `FARWeightedTNFExample.lean`.

**Source-checked.** The full canonical + weighted-TNF import closure and both concrete examples passed [CI 45389105512](https://github.com/FlareZ123/bb6/actions/runs/45389105512). The workflow rejects `sorryAx` and `native_decide` in the closure output. This is a reusable proof-interface result, not a BB(6) upper bound: the firstOne root still needs a closed audit or a complete weighted-TNF tree.



## SMT synthesis for hard partial tables (24 November 2026)

The existing `far_smt.py` searches the same finite-automata certificate constraints as the Lean FAR checker, using an implication-per-intermediate-state Z3 encoding. The new `far_smt_compose.py` uses QF_BV and caches the composed NFA successor mask
`⋃ { E_write[v] | v ∈ E_oldLeftBit[intermediate] }`,
then requires that mask to be a subset of the current configuration's successor mask. This is exactly the same left-move inclusion condition, factored as one bit-vector inclusion per predecessor-DFA state and old-left symbol. DFA-state bounds use unsigned comparisons. Candidate models remain untrusted and must pass the workflow's independent Lean `Data.fastValid_sound` check before they can be promoted to a proof.

The manual workflow `.github/workflows/agent7-far-hard-root.yml` now supports:
- `solver_encoding=implications|compose`;
- an exact roster `solver_line`, or an arbitrary 12-slot `solver_code` override for a concrete TNF node;
- independent Lean verification of every emitted hit.

Bounded search status (24 November 2026):
- #746 roster line 618, implication encoding, run [45400338305](https://github.com/FlareZ123/bb6/actions/runs/45400338305): both orientations UNSAT at DFA sizes 6–8; both orientations timed out at sizes 9–10.
- #746, composed encoding, run [45401745777](https://github.com/FlareZ123/bb6/actions/runs/45401745777): both orientations UNSAT at sizes 6–7; reflected size 8 UNSAT; unreflected size 8 and both orientations at sizes 9–10 timed out.
- Roster line 221, composed encoding, run [45404101670](https://github.com/FlareZ123/bb6/actions/runs/45404101670): both orientations UNSAT for DFA sizes 1–5.
- Roster line 335, composed encoding, run [45402030399](https://github.com/FlareZ123/bb6/actions/runs/45402030399): pending.
- The r1 F/1=`0LB` sibling is already covered by `Growth.zBD false` in `im-results/agent47-r1-sweep/R1Parent.lean` and assembled by `R1Graft.r1_certificate`; do not treat the earlier FAR probe as a new frontier leaf.
- Regression test on the existing four-transition glider, run [45404260897](https://github.com/FlareZ123/bb6/actions/runs/45404260897): recovered the existing one-state certificate exactly (DFA [0,0], masks [2,1,1,64,64,64,64] / [4,64,64,64,64,64,64], zero mask 120); Lean accepted the generated theorem with standard axioms only.

These are candidate-search experiments, not impossibility results. A timeout is not UNSAT, and a bounded failure to synthesize a FAR certificate says nothing about whether the machine halts. The glider run is only a regression against a known certificate, not a new machine result. Any successful hard-root leaf must also be shown to occur in the actual first-one weighted-TNF/Enumerate62 coverage, not merely in the historical 663-entry roster.
