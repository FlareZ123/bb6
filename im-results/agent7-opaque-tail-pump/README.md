# Raw36 D1=0LA: all seven exceptional literals resolved

**28 November 2026; Agent 7.** All seven literals outside the archived 2,218-candidate union and the 30 earlier source-certified closures now have exact original-source Lean theorems. Three are nonhalting for every compatible completion; four have exact first-hole exposures with universal weighted bounds. The full 2,255-literal OPEN census is thus covered by computational candidate evidence and individual proofs. **The full D100 parent Cover remains unproved until the 2,218 archived candidates are individually checked and assembled with the exhaustive tree.**

## Exceptional literals

| Literal | Exact result | Evidence |
|---|---|---|
| `1RB0LE_1RC1LD_0RD0RB_0LD0LA_1LA0RF_1RE---` | Universal nonhalting by alternating-word countdown/doubling | [COUNTDOWN.md](COUNTDOWN.md); `D100CountdownNever.lean` |
| `1RB1LA_1RC1LE_0RD0LB_0LD0LA_---0LF_1LC0RA` | Universal nonhalting by unary doubling | [UNARY-DOUBLE.md](UNARY-DOUBLE.md); `D100UnaryDouble.lean` |
| `1RB1LA_1RC1LE_0RD1RE_0LD0LA_1RF0LB_1LD---` | F1 after 4,672,258; weighted bound 4,672,264 | `D100FiniteF1.lean`, `D100FiniteF1Trace.lean` |
| `1RB1LA_1RC1LE_0RD1RF_0LD0LA_---0LB_1LD1RB` | E0 after 53,257,978,073,992,275; weighted bound 53,257,978,073,992,281 | [DELAYED-E0.md](DELAYED-E0.md); `D100DelayedBound.lean` |
| `1RB1LE_1RC---_0RD1RF_0LD0LA_0LB0LA_1LA1RB` | B1 after 60,671; weighted bound 60,677 | [CI 46151144864](https://github.com/FlareZ123/bb6/actions/runs/46151144864) |
| `1RB1RE_1RC---_0RD1RA_0LD0LA_1LD0RF_0RE1RC` | Universal nonhalting by 78-cell opaque-tail pump, period 2,396,150, entry 2,396,162 | [LONG-EPOCH.md](LONG-EPOCH.md); [CI 46150968383](https://github.com/FlareZ123/bb6/actions/runs/46150968383) |
| `1RB1RE_1RC1LF_0RD1RF_0LD0LA_1LA1LE_---0LB` | F0 after 23,126; weighted bound 23,132 | [CI 46151140947](https://github.com/FlareZ123/bb6/actions/runs/46151140947) |

The first four rows compile locally with Lean 4.36.0-rc2 using exact original-source dependencies, whose blob IDs and root axiom profiles are recorded in [SOURCE-CHECK.md](SOURCE-CHECK.md). The last three rows have successful original-source CI proof jobs. The finite exposures are not nonhalting theorems: the halt completion stops at the first query, all other completions are total and run forever. The generic `Run0LastHole.lean` bridge bounds the weighted score by n+6 without reducing millions or quadrillions of primitive steps.

The F1 exposure proof uses 22 accelerated epochs. Writing U(n)=1^n, V=1010 and B(j,R)=(B,[],0V^jR), the exact uniform step law is B(j,111R)→B(j+1,R) in 12j+11 steps. Induction consumes 3a ones in 12ja+6a²+5a steps. For A(n,S)=(A,[],U(n)S), n=3j+r>0, the scan reaches (C,01U(4j),U(r)S) after 6j²+13j+4 moves. Each of the 21 ordinary epoch boundaries is a constant-size arbitrary-tail transition identity followed by a unary sweep; the last boundary reaches F1 in six moves. The exact final configuration is (F,1^2334,0^19 10). The root theorem `BB6.Agent7D100FiniteF1.bound` uses only propext, Classical.choice, Quot.sound. No simulation oracle or sorryAx.

## Exact census and coverage accounting

The original direct scout [run 46122807180](https://github.com/FlareZ123/bb6/actions/runs/46122807180), artifact **15254765346**, contains a 1,378,849-node source-indexed tree over parent
'1RB---_1RC---_0RD---_0LD0LA_------_------' with **2,255** distinct canonical OPEN literal tables. SHA256 of sorted, underscore-stripped literals joined by '\n':
'd3cff2c1257272d8af4c8087906589d4623f41dcd8cd3de98e2ae7f71d8d8ff0'.

Archived FAR candidate bank [run 46123250654](https://github.com/FlareZ123/bb6/actions/runs/46123250654), artifact 15255135843, supplies **1,773** keys; inverse-stack N-gram bank [run 46123330768](https://github.com/FlareZ123/bb6/actions/runs/46123330768), artifact 15254647345, supplies **883**, sharing **706**, for a **1,950** union. Structured RLE/modular/phase bank [run 46137226038](https://github.com/FlareZ123/bb6/actions/runs/46137226038), artifact 15259619077, adds **268** unique keys. These **2,218** are *computational candidate certificates*, NOT yet a single source-accepted D100 parent proof.

Earlier incarnations constructed **30 additional, pairwise distinct** literal nonhalting theorems for tables outside those 2,218 keys. **All 30 have passed original-source Lean 4.36.0-rc2 audit**. The exact-key sets and independent accepted runs are:

| Set | Files / source mode | Count | Accepted CI |
|---|---|---:|---|
| Opaque arbitrary-tail pumping | 'd100-new-pumps.txt', 'pump_emit.py' | 7 | [46137768105](https://github.com/FlareZ123/bb6/actions/runs/46137768105) |
| Modular-base inverse stacks | 'd100-new-modular.json', 'emit_modular.py five' | 5 | [46138236685](https://github.com/FlareZ123/bb6/actions/runs/46138236685) |
| Extended modular and run-length stacks | 'd100-new-modular-extra.json', 'emit_modular.py six' | 6 | [46138631835](https://github.com/FlareZ123/bb6/actions/runs/46138631835) |
| Finite-phase quotient automata | 'd100-new-phase-ten.json', 'emit_modular.py ten' | 10 | [46138780012](https://github.com/FlareZ123/bb6/actions/runs/46138780012) |
| Additional finite-phase quotients | 'd100-new-phase-two.json', 'emit_modular.py two' | 2 | [46139124988](https://github.com/FlareZ123/bb6/actions/runs/46139124988) |

For every exported 'never' theorem the original Lean source closure compiled and audit listed only '[propext, Quot.sound]'; there is no 'sorryAx' or 'native_decide'. Exact table-key membership was asserted against the original 2,255 OPEN census before theorem generation. The source-accepted **30** and 2,218 existing candidate keys are disjoint, leaving exactly **7** exceptional literals outside this combined *candidate* union. SHA256 of sorted seven exact underscore-bearing literals joined by '\n':
'd2c1461685beee42b0f5ad19d75fd13ffb843c6572dbc2ec4907f96a9556e88a'.

The 2,218 archived candidates are discovery evidence, not yet accepted source closures. All 37 individual closures (30 earlier and 7 exceptional) now have exact-key proofs, 33 through CI and 4 through local original-source compilation. No global residual count or whole parent proof is asserted here.

## Next decisive work

Assemble the exhaustive D100 parent with common weighted bound at least 53,257,978,073,992,281. Reuse the existing tree and candidate banks; check the 2,218 archived witnesses in bounded batches, then transport their literal theorems into the authenticated exhaustive tree together with the 37 individual closures. Do not rerun already resolved hard machines. Coordinate the shared CI gate with Agent29 and the canonical consumers.

Historical candidate detection and generators remain in this directory: `detect_pump.py`, `pump_emit.py`, `emit_modular.py`, `long_epoch_certificate.py`, `exposure_emit.py`, and the existing parameterized workflow.
