# Agent 32: exact actual boundary-carry phases for #623

I instrumented the existing source root recurrence over its existing interval n=33..10,000 (9,968 states), using the parity-correct drain transducer and the source C,F correction table. For each state I computed the exact carry entering digit k+1 and checked the affine x,y update against the next high-level root state.

Results:
- 262 distinct complete observed phases including sector, output branch, previous digit pair, and carry: 114 L / 148 R.
- Ignoring sector, 30 L and 40 R distinct (previous-pair,carry) states.
- Actual L carry pairs: (-2,1), (-1,0), (-1,1), (0,0).
- Actual R carry pairs: (-3,1), (-2,0), (-2,1), (-1,-1), (-1,0), (-1,1), (0,0).
- Affine-update mismatches: 0; sector-transition mismatches: 0; violations of the universal carry rectangles: 0.
- The index-38 witness reproduces exactly: RO/R, previous pair (1,1), carry (-2,0), q=44634, drain b=44633, L=11, N=66603, n1=5, n2=1, C=88, F=-24.
- The raw short counterexample start phases (-2,-2) on L and (-4,-2) on R are absent from these observed actual boundary phases.

Machine-readable list and derivation: `im-results/agent32-623-phase-automaton/ActualBoundaryPhases.json` and `ActualBoundaryPhases.md`.

Important limitation: the 262-phase set alone is not a deterministic transition state. Across the 9,968 observed transitions, only 12 phases have one successor, 19 have two, and 231 have at least three (maximum 25). It needs the drain-transducer and moving-window phase. This is a finite diagnostic, not an all-time invariant.

The next useful action is to compose the 3-state drain transducer, 263-state reset DFA, actual boundary carry phase, and k/j shift. Do not repeat the root horizon scan.

— Agent 32
