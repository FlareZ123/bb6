# Reset-language nonclosure under the raw branch transducers

**Status:** exact finite counterexamples. These falsify unrestricted reset preservation for the full L/R carry rectangles. They do **not** contradict the authentic-root scan: blank-root digit windows and boundary phases satisfy additional arithmetic restrictions not imposed here.

The 263-state DFA in ResetPatternDFA.json recognizes words containing a common reset pattern of length 3--6. The reset patterns below are checked against every start state in both full carry rectangles.

## Corrected length-three witnesses

The L-branch output in the earlier version of this note was mistyped. With the published L transducer
\[
r_x=x_i-y_{i-1}+a_i,\qquad r_y=y_{i-1}+b_i,
\]
the start state \((x_{-1},y_{-1},a,b)=(0,0,-2,-2)\) and input
\[
W_L=(00,02,00)
\]
give
\[
U_L=(11,22,01),
\]
not \((11,02,10)\). The reset DFA rejects this output. Directly checking all 225 L starts and all 270 R starts shows that 00 02 00 is a common reset pattern: it synchronizes both branch transducers to \((x_{\rm prev},y_{\rm prev},a,b)=(0,0,-1,0)\), and every trajectory's x-output is nonmonochromatic.

For the R branch, the full-range start state \((0,0,-4,-2)\) and input
\[
W_R=(00,01,00)
\]
give
\[
U_R=(21,12,10).
\]
The reset DFA rejects this output. The word 00 01 00 is also a common reset pattern for both full start rectangles and has the same synchronized final state \((0,0,-1,0)\).

## Eight-symbol moving-window counterexamples

Using the conservative source buffer
\[
B_S=\max(34\ell_S+140,\ 36\ell_S+88),
\]
the finite root scan from \(D_{33}\) through \(D_{10000}\) has S-window lengths 8--16. The following witnesses therefore match the **minimum observed safe-window length**, while covering all three algebraically allowed shifts \((k'-k,j'-j)\in\{(0,0),(0,1),(1,1)\}\).

| Branch / sector label | Shift | Input window | High extension | Target output window |
|---|---:|---|---|---|
| L / LO | (0,0) | 00 02 00 10 20 00 20 00 | — | 11 22 01 00 20 00 20 00 |
| L / LO | (0,1) | 00 02 00 10 20 00 20 00 | 00 | 11 22 01 00 20 00 20 00 00 |
| L / LO | (1,1) | 00 02 00 00 00 00 00 10 | 00 | 22 01 20 20 20 20 00 00 |
| R / RO | (0,0) | 00 01 00 20 10 20 00 10 | — | 21 12 10 00 22 11 22 00 |
| R / RO | (0,1) | 00 01 00 20 10 20 00 10 | 00 | 21 12 10 00 22 11 22 00 11 |
| R / RO | (1,1) | 00 01 00 20 00 00 20 00 | 00 | 12 10 00 02 20 00 02 20 |

Each input window contains a common reset pattern by symbol 3. Every listed input and output x-block contains at least one digit different from 0 and at least one digit different from 2. The output window contains **no** common reset pattern. All intermediate carries remain within L's \([-2,2]\times[-2,2]\) or R's \([-4,1]\times[-2,2]\) rectangle.

The branch/sector labels are compatible examples (LO/L and RO/R); they do not assert that the chosen boundary states are reachable from the blank root. The high-extension symbols are unconstrained. These are counterexamples to closure under the unrestricted full carry rectangles and allowed window shifts, not counterexamples on the authentic #623 orbit.

## Reproduction

Run from the repository root:
\`\`\`sh
node im-results/agent32-623-phase-automaton/full_range_window_counterexamples.js
\`\`\`

The script verifies both reset patterns against all 495 full-range starts, checks every carry transition in the six witnesses, checks the input/target x-block nonmonochromatic conditions, and asks the committed 263-state DFA to accept the input and reject the shifted output.

## Consequence

The reset recognizer, full carry rectangles, sector/branch labels, nonmonochromaticity, and the three allowed window shifts are still insufficient for an invariant. The product must retain a **source-derived restriction on authentic root windows and/or their weighted-drain history**. The finite observed phase sets are not substitutes for such a theorem. Keep the index-33 whole-window failure as a separate regression case.
