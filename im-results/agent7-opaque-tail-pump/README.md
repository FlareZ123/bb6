# Raw36 D1=0LA: source-certified finite-quotient and opaque-tail frontier

**28 November 2026; Agent 7.** This is an intermediate, reproducible research dossier, **not** a claim that the complete D1=0LA parent Cover or BB(6) is proved.

## Exact census and coverage accounting

The original direct scout [run 46122807180](https://github.com/FlareZ123/bb6/actions/runs/46122807180), artifact **15254765346**, contains a 1,378,849-node source-indexed tree over parent
'1RB---_1RC---_0RD---_0LD0LA_------_------' with **2,255** distinct canonical OPEN literal tables. SHA256 of sorted, underscore-stripped literals joined by '\n':
'd3cff2c1257272d8af4c8087906589d4623f41dcd8cd3de98e2ae7f71d8d8ff0'.

Archived FAR candidate bank [run 46123250654](https://github.com/FlareZ123/bb6/actions/runs/46123250654), artifact 15255135843, supplies **1,773** keys; inverse-stack N-gram bank [run 46123330768](https://github.com/FlareZ123/bb6/actions/runs/46123330768), artifact 15254647345, supplies **883**, sharing **706**, for a **1,950** union. Structured RLE/modular/phase bank [run 46137226038](https://github.com/FlareZ123/bb6/actions/runs/46137226038), artifact 15259619077, adds **268** unique keys. These **2,218** are *computational candidate certificates*, NOT yet a single source-accepted D100 parent proof.

This invocation constructed **30 additional, pairwise distinct** literal nonhalting theorems for tables outside those 2,218 keys. **All 30 have passed original-source Lean 4.36.0-rc2 audit**. The exact-key sets and independent accepted runs are:

| Set | Files / source mode | Count | Accepted CI |
|---|---|---:|---|
| Opaque arbitrary-tail pumping | 'd100-new-pumps.txt', 'pump_emit.py' | 7 | [46137768105](https://github.com/FlareZ123/bb6/actions/runs/46137768105) |
| Modular-base inverse stacks | 'd100-new-modular.json', 'emit_modular.py five' | 5 | [46138236685](https://github.com/FlareZ123/bb6/actions/runs/46138236685) |
| Extended modular and run-length stacks | 'd100-new-modular-extra.json', 'emit_modular.py six' | 6 | [46138631835](https://github.com/FlareZ123/bb6/actions/runs/46138631835) |
| Finite-phase quotient automata | 'd100-new-phase-ten.json', 'emit_modular.py ten' | 10 | [46138780012](https://github.com/FlareZ123/bb6/actions/runs/46138780012) |
| Additional finite-phase quotients | 'd100-new-phase-two.json', 'emit_modular.py two' | 2 | [46139124988](https://github.com/FlareZ123/bb6/actions/runs/46139124988) |

For every exported 'never' theorem the original Lean source closure compiled and audit listed only '[propext, Quot.sound]'; there is no 'sorryAx' or 'native_decide'. Exact table-key membership was asserted against the original 2,255 OPEN census before theorem generation. The source-accepted **30** and 2,218 existing candidate keys are disjoint, leaving exactly **7** outside this combined *candidate* union. SHA256 of sorted seven exact underscore-bearing literals joined by '\n':
'd2c1461685beee42b0f5ad19d75fd13ffb843c6572dbc2ec4907f96a9556e88a'.

The 7 unresolved literal keys:
\`\`\`
1RB0LE_1RC1LD_0RD0RB_0LD0LA_1LA0RF_1RE---
1RB1LA_1RC1LE_0RD0LB_0LD0LA_---0LF_1LC0RA
1RB1LA_1RC1LE_0RD1RE_0LD0LA_1RF0LB_1LD---
1RB1LA_1RC1LE_0RD1RF_0LD0LA_---0LB_1LD1RB
1RB1LE_1RC---_0RD1RF_0LD0LA_0LB0LA_1LA1RB
1RB1RE_1RC---_0RD1RA_0LD0LA_1LD0RF_0RE1RC
1RB1RE_1RC1LF_0RD1RF_0LD0LA_1LA1LE_---0LB
\`\`\`

## Mathematical source-checking methods

The 'detect_pump.py' procedure detects an *untrusted candidate* exact step law
'run0 p D (q,F,P ++ R) = some (q,F,P ++ W ++ R)' **uniformly for every arbitrary tape suffix R**, with nonempty W and D>0. It refuses to read an opaque '?' marker when checking candidate macros. Its corresponding 'pump_emit.py' emits finite 'by rfl' original-machine transition laws, an authentic segmented blank-entry proof, an infinite growth induction, and an all-compatible-total-completions 'NeverHalts' theorem. Reflected left-ray variants are supported. The original 902-step D1=0LB certificate was used only as regression and is not counted anew.

The 'emit_modular.py' path uses the original 'stack_candidates.generate' finite two-sided automata prover. Our novel search extended modular bases to **1,3,5,6,8 and beyond** instead of the earlier narrow bank, broadened bounded run-length states, and sampled finite phase quotients. Discovery itself is not trusted: each generated certificate is accepted only through the independently compiled original 'TwoSidedAutomata' source and an explicit axiom audit. The existing parameterized manual CI workflow '.github/workflows/agent7-raw36-drift902.yml' performs these source gates.

## Important distinction: finite first-hole exposures

A literal partial machine with exactly one missing row and **all other defined instructions nonhalting**, whose blank computation first queries that row after n transitions, has the elementary completion dichotomy: every compatible total machine either has a nonhalting instruction at that row, in which case it **never halts**, or has a halting instruction there, in which case it **halts at the first query**. The F0 and B1 exposure times below and their all-completions weighted upper bounds are now original-source Lean 4.36.0-rc2 theorems. The F1 exposure time remains simulation-only:

| Literal key | Sole missing row | First query after |
|---|---|---:|
| '1RB1RE_1RC1LF_0RD1RF_0LD0LA_1LA1LE_---0LB' | F0 | 23,126 steps |
| '1RB1LE_1RC---_0RD1RF_0LD0LA_0LB0LA_1LA1RB' | B1 | 60,671 steps |
| '1RB1LA_1RC1LE_0RD1RE_0LD0LA_1RF0LB_1LD---' | F1 | 4,672,258 steps |

The F0 and B1 times were independently reproduced by `exposure_scan.cpp` and source-faithful two-stack simulation. The original-source `exposure_emit.py` gives exact segmented `run0` theorems (`reached`, `hole`), and `Run0ExposureBound.lean` plus `emit_exposure_bound.py` connect them to `BB6.Agent7D100ExposureBound.bound` over **all compatible total completions**. Source-accepted run [46151140947](https://github.com/FlareZ123/bb6/actions/runs/46151140947) establishes `WeightedBound 23132` for F0; source-accepted run [46151144864](https://github.com/FlareZ123/bb6/actions/runs/46151144864) establishes `WeightedBound 60677` for B1. Each compiled 54 original-source Lean modules, the exported `bound` theorem uses only `[propext, Classical.choice, Quot.sound]`, and neither run used `sorryAx` or `native_decide`. These are conservative exact upper bounds, not claims of minimum weighted thresholds. The F0 source uses 137 chunks, sha256 `520970e8e17cd2a0bcc882d5fe872a602616316884102444c1a45d5981085935`; B1 119 chunks, sha256 `b7dd63eefcfab9fa14f933dcf182f97594e7e89e720c276bff1b48b1174fc456`. The F1 4,672,258-step exposure is **simulation only** and its global weighted bound remains to be source checked.

The **other four** residual literals did not query their missing row within 300,000,000 simulated blank-tape steps each; that alone cannot establish nonhalting. One of these four—the hard B1 literal `1RB1RE_1RC---_0RD1RA_0LD0LA_1LD0RF_0RE1RC`—now has an exact **2,396,150-step 78-cell arbitrary-left-suffix pumping candidate**, which grows an inductive family after an exact blank entry at step 2,396,162. The source-faithful symbolic replay does not read an opaque unknown tape suffix. Reproduction, 78-bit word and source-checkable generated Lean modules are in [LONG-EPOCH.md](LONG-EPOCH.md) and `long_epoch_certificate.py`; the first two source batches compiled in pilot run 46150569160. The full `never` source/axiom audit was dispatched in run [46150968383](https://github.com/FlareZ123/bb6/actions/runs/46150968383), and must succeed before this case may be reported as a formally closed nonhalting leaf. The remaining three persistent cases require stronger invariants. One, the E0-hole literal `1RB1LA_1RC1LE_0RD0LB_0LD0LA_---0LF_1LC0RA`, now has an exact all-time unary-doubling recurrence with local Lean-checked entry and growth; the original-source `never` bridge awaits acceptance. See [UNARY-DOUBLE.md](UNARY-DOUBLE.md).

## Next decisive work

* The F0 and B1 finite-exposure weighted bounds are **now original-source accepted**, so do not rerun them. Close the F1 4,672,258-step finite exposure with a source-accepted bound, preferably exploiting macro structure rather than recomputing huge traces.
* **Finish** the original-source acceptance of the new constant-cost B1 opaque-tail 78-cell pump, then develop genuinely new invariants for the other **three** persistent literal cases; asymmetric finite n-grams, mixed finite quotients and short-horizon single-/double-ray opaque-tail insertion had not certified them.
* **Accept the 2,218 archived candidates individually in Lean**, then assemble the **complete** source-checked D100 parent audit; do not confuse 2,248 distinct candidate-covered keys with an accepted 'Cover', or promote this dossier into 'results/' until the larger mathematical claim is proved.

The E0-hole literal `1RB1LA_1RC1LE_0RD1RF_0LD0LA_---0LB_1LD1RB` is now resolved at the reconstructed-model level by an exact accelerated exposure of 53,257,978,073,992,275 transitions. See [DELAYED-E0.md](DELAYED-E0.md). Original-source WeightedBound acceptance is pending; no accepted global count changed.

The final persistent F1-hole literal `1RB0LE_1RC1LD_0RD0RB_0LD0LA_1LA0RF_1RE---` is now resolved at the reconstructed-model level by a universal countdown/doubling/restart recurrence with exact positive-cost induction. See [COUNTDOWN.md](COUNTDOWN.md). The original-source `NeverHalts` bridge still awaits acceptance. All three formerly persistent hard literals now have local model-checked mathematical certificates.
