# S-indexed own-start phase under the conservative source buffer

**Status:** finite diagnostic on \(D_{33},\ldots,D_{10000}\). This replaces the earlier 34ℓ+122-only phase count, which depended on the sharper source bridge before a pinned compile.

## Conservative S-window

Until the newer DrainDigitSourceBridge.lean theorem has a successful pinned Lean run, use the already source-supported coordinate envelope
\[
B_S=\max(34\ell_S+140,\ 36\ell_S+88).
\]
For each state, \(k\) and \(j\) are the least exponents with \(3^k>B_S\) and \(3^j>B_S^3\), and the S-window is \([k+2,j-2)\).

A replay of the exact high-level root recurrence over 9,968 states gives:
- \(\ell_S\) range: 11--1,937;
- the \(34\ell_S+140\) term is maximal for 80 states; \(36\ell_S+88\) is maximal for 9,888;
- S-window lengths: 8--16;
- **zero** windows fail the 263-state common-reset DFA;
- first-reset end-position histogram: 3:2196, 4:4210, 5:2241, 6:866, 7:290, 8:105, 9:37, 10:14, 11:6, 12:3.

This reset scan uses the conservative buffer and does not rely on the uncompiled \(34\ell_S+122\) source bridge.

## Own-start phase definition

For a root state \(D(a,d)\), compute its own sector, branch, and drain input
\[
b=q+\begin{cases}3&LO\\2&LE\\-1&RO\\1&RE.\end{cases}
\]
The source-summary recurrence in DrainDigitSourceBridge.lean gives \((L,E,R)\), where \(D=L-2E\) is the first-counter drop and \(R\) is the full evaluator-call count. Apply the exact source correction formulas from SignedCoordinateNormalForm.lean to obtain \(C,F\).

With \(k\) from the conservative S-window, sourceCarry gives the carry entering digit \(k+1\), and the previous pair is \((x_k,y_k)\). Advance the state's own digit pair at \(k+1\) once through its own branch transducer. The resulting previous pair and carry are the state entering the first symbol \(k+2\) of the S-window. The finite key is
\[
(\mathrm{sector},\mathrm{branch},(x_{k+1},y_{k+1}),(c'_a,c'_b),r),
\qquad r=j-3k.
\]

The phase calculation is a literal JavaScript replay of sourceDrainSummary and the source correction formulas. The Lean source theorem is present but was not compiled in this invocation; treat the phase counts as a diagnostic pending that compile. The conservative reset scan above is independent of these exact phase values.

## Distinction from the 1,318 source-to-target transition keys

For an edge \(D_n\to D_{n+1}\), Agent 48's phaseForTransition(source,target) starts with the source correction and source branch, then consumes source digits through \(k'+1\). Its returned carry/previous pair is the source-to-target transducer state entering the target word. The own-start phase instead recomputes the target's own drain summary and correction, then advances one target digit. These are different phase meanings.

On the 9,967 edges \(D_{33}\to D_{10000}\), the source-to-target (branch,prev,carry) and the target's own-start (branch,prev,carry) differ on **9,739** edges (228 agree). The projected carry-pair sets are not sufficient to identify the full phase.

## Finite diagnostic for the own-start key

Across the 9,968 states \(D_{33},\ldots,D_{10000}\):
- **697** distinct own-start phase keys;
- 4,549 distinct directed edges between consecutive observed keys;
- 616 keys have multiple observed successors;
- maximum observed outdegree: **20**.

Outdegree histogram (degree: number of keys):
\[
1:81,\ 2:77,\ 3:80,\ 4:44,\ 5:31,\ 6:44,\ 7:51,\ 8:52,\ 9:52,\ 10:57,
\]
\[
11:32,\ 12:32,\ 13:19,\ 14:19,\ 15:13,\ 16:4,\ 17:4,\ 18:4,\ 20:1.
\]

First states:
| Index | Sector / branch | Previous pair | Carry | \(r\) | \(k,j\) | Window length |
|---:|---|---|---|---:|---:|---:|
| 33 | RO / R | (0,0) | (-2,1) | 0 | (6,18) | 8 |
| 34 | RE / L | (2,0) | (0,0) | 0 | (6,18) | 8 |
| 35 | LO / R | (1,1) | (-1,0) | 0 | (6,18) | 8 |
| 36 | RO / R | (1,0) | (-2,0) | 0 | (6,18) | 8 |
| 37 | RE / R | (2,2) | (-2,0) | 0 | (6,18) | 8 |

The own-start key is still not a deterministic state on the observed orbit: 616 keys have multiple observed successors. This is finite evidence only, not an all-time transition theorem or a root invariant.

## Integration point

Keep both phases in any future product:
1. source-to-target phase proves the current output-digit correspondence;
2. target own-start phase initializes the next edge.

Do not relabel the 1,318 transition keys as the own-start phase set. A closed product still needs a source-derived weighted-drain/root-language restriction and a successful source/Lean validation of the phase interface.
