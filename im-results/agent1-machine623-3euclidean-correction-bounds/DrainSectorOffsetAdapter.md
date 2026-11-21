# Two-digit sector-offset adapter for the #623 drain transducer

**Status:** exact finite-state algebraic reduction from the existing three-state transducer and its proved ±1 offset identities. The table was exhaustively cross-checked for lengths 2–7 (6,552 cases) in a separate JavaScript implementation. The new adapter itself has not yet been Lean-formalized. It is an intermediate interface, not a root-history invariant or a nonhalting proof.

## Purpose

For a canonical state with smaller coordinate \(q\), the four source sectors call the full drain with counter

| Sector | Drain counter |
|---|---:|
| LO | \(q+3\) |
| LE | \(q+2\) |
| RO | \(q-1\) |
| RE | \(q+1\) |

The three-state transducer reads the low-to-high ternary digits of this counter, starting in state A. Existing \`DrainDigitOffsetStats.lean\` proves the output-and-count identities

\[
\mathcal S_n(q+1,A)=\mathcal S_n(q,C),\qquad
\mathcal S_n(q,B)=\mathcal S_n(q-1,A),
\]

where \(\mathcal S_n(b,s)\) records the emitted integer and the counts of output digits 1 and 2 in the low \(n\) positions. The identities are valid for the low-\(n\)-digit words, including the exact \(3^n\) boundary for output/counts. Final transducer-state equality has a stricter no-overflow hypothesis.

Thus the two right-sector inputs normalize immediately to the common digit stream of \(q\), with initial states C (RE) and B (RO). The left-sector offsets \(+2,+3\) can also be reduced to that same stream after exposing two low digits.

## Exact two-digit adapter

Let \(n\ge2\), let \(q_0=q\bmod 3^n\), and write

\[
q_0=9Q+r,\qquad 0\le r<9.
\]

For \(c\in\{2,3\}\), run the transducer on the low-\(n\)-digit word of \(q+c\), starting in A. The first two input digits are the low-to-high digits of \((q_0+c)\bmod 3^n\). They emit the prefix shown below. After those two digits, the remaining suffix is \(Q\) in the listed normalized initial state \(s_*\).

The prefix output digits are listed low-to-high as \((o_0,o_1)\). Define

\[
P=o_0+3o_1,\qquad
R_0=\#\{i\in\{0,1\}:o_i\ne0\},\qquad
E_0=\#\{i\in\{0,1\}:o_i=2\}.
\]

| \(r=q\bmod9\) | \(c=2\): input digits | output digits | \(P\) | \(R_0\) | \(E_0\) | \(s_*\) |
|---:|---:|---:|---:|---:|---:|:---:|
| 0 | (2,0) | (0,1) | 3 | 1 | 0 | A |
| 1 | (0,1) | (2,2) | 8 | 2 | 2 | B |
| 2 | (1,1) | (1,1) | 4 | 2 | 0 | A |
| 3 | (2,1) | (0,0) | 0 | 0 | 0 | C |
| 4 | (0,2) | (2,1) | 5 | 2 | 1 | A |
| 5 | (1,2) | (1,0) | 1 | 1 | 0 | C |
| 6 | (2,2) | (0,2) | 6 | 1 | 1 | A |
| 7 | (0,0) | (2,0) | 2 | 1 | 1 | C |
| 8 | (1,0) | (1,2) | 7 | 2 | 1 | A |

| \(r=q\bmod9\) | \(c=3\): input digits | output digits | \(P\) | \(R_0\) | \(E_0\) | \(s_*\) |
|---:|---:|---:|---:|---:|---:|:---:|
| 0 | (0,1) | (2,2) | 8 | 2 | 2 | B |
| 1 | (1,1) | (1,1) | 4 | 2 | 0 | A |
| 2 | (2,1) | (0,0) | 0 | 0 | 0 | C |
| 3 | (0,2) | (2,1) | 5 | 2 | 1 | A |
| 4 | (1,2) | (1,0) | 1 | 1 | 0 | C |
| 5 | (2,2) | (0,2) | 6 | 1 | 1 | A |
| 6 | (0,0) | (2,0) | 2 | 1 | 1 | C |
| 7 | (1,0) | (1,2) | 7 | 2 | 1 | A |
| 8 | (2,0) | (0,1) | 3 | 1 | 0 | C |

In every row, the two-digit prefix followed by the transducer on \(Q\) in state \(s_*\) reproduces the output and both digit counts for the original \(n\)-digit input. In particular, writing \((O,U,V)=\mathcal S_n((q+c)\bmod3^n,A)\),

\[
O=P+9O_*,\qquad U=R_0+U_*,\qquad V=E_0+V_*,
\]

where \((O_*,U_*,V_*)=\mathcal S_{n-2}(Q,s_*)\).

### Why the carry rows normalize

For \(c=2\), the only rows with \(r+c\ge9\) are \(r=7,8\); for \(c=3\), they are \(r=6,7,8\). After the first two digits, these rows leave suffix \(Q+1\) in state A or B, respectively. The existing offset identities replace

\[
\mathcal S_{n-2}(Q+1,A)=\mathcal S_{n-2}(Q,C),\qquad
\mathcal S_{n-2}(Q+1,B)=\mathcal S_{n-2}(Q,A).
\]

No carry row leaves state C, so these two identities cover every case. The non-carry rows leave suffix \(Q\) directly in the state displayed in the table.

## Consequence for the exact correction weights

The source drain normal form uses

\[
D=L-2E_{\rm dig},\qquad
R_{\rm dig}=n_1+n_2,
\]

where \(L\) is the full transducer length, \(E_{\rm dig}\) is the number of output 2-digits, and \(R_{\rm dig}\) is the number of nonzero output digits. For the \(+2,+3\) adapters, the table gives the exact decomposition

\[
D=(L-2)-2V_*+2-2E_0,\qquad
R_{\rm dig}=U_*+R_0.
\]

For the right sectors, the existing ±1 identities give the same weights directly from the \(q\)-word, with initial state B (RO) or C (RE). The full source evaluator-call count is already identified with \(R_{\rm dig}\) by the existing source bridge; in RE, retain the documented full-versus-split convention when forming the sector threshold.

The high ternary digit of \(q+c\), when present, is not part of the low-\(L\)-digit output/count calculation. It remains governed by the existing \`drain_transducer_exact_of_bounds\` theorem and its size/parity hypotheses. The adapter therefore preserves exactly the quantities needed by the weighted correction formulas; it does not assert equality of final transducer states at an overflow boundary.

## Proof route for Lean packaging

A compact formalization can proceed by:

1. Define a two-step prefix summary from the two applications of \`step\` in \`DrainDigitTransducerCarry.lean\`.
2. Split \(r\in\{0,\ldots,8\}\) and \(c\in\{2,3\}\), unfolding the two low-digit transitions.
3. In the carry rows, apply the already proved \`runStatsData_offset_identities\` at length \(n-2\).
4. Reassemble output value and counts using the base-3 positional factor 9.
5. Keep the high-digit/terminal-phase argument separate, using the existing exact drain theorem.

This avoids re-proving the source evaluator recursion and makes the sector dependence an explicit finite prefix table.

## Validation and scope

A separate JavaScript implementation of the exact nine transducer transitions exhaustively checked every \(q_0\in[0,3^n)\), both \(c=2,3\), and every \(n=2,\ldots,7\): 6,552 cases, with zero output or count mismatches. This is a debugging cross-check, not a Lean proof.

The reduction removes the need to treat the four sector offsets as four unrelated long ternary inputs. It does **not** establish closure of the root's moving-window phase, exclude a terminal strip, prove that the authentic \(D(0,7)\) orbit is infinite, or determine BB(6).
