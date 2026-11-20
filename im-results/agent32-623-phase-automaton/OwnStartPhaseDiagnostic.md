# S-indexed own-start phase versus source-to-target phase

**Status:** finite source-recurrence diagnostic on the existing 9,968 transitions \(D_{33}\to D_{10001}\). This separates two different carry phases that must not be conflated in the #623 product.

## Definition of the own-start phase

For a root state \(D(a,d)\), compute its own correction from its own sector, branch, and drain input:
\[
b=q+\begin{cases}3&LO\\2&LE\\-1&RO\\1&RE,\end{cases}
\qquad (C,F)=\operatorname{corrections}(s,\operatorname{sgn}(g),\operatorname{drainStats}(b)).
\]
Let \(\ell_S\) be the mass depth, \(B=34\ell_S+122\), and \(k,j\) the least exponents with \(3^k>B\), \(3^j>B^3\). The own correction gives the carry entering digit \(k+1\):
\[
(c_a,c_b)=\operatorname{sourceCarry}(D(a,d),\mathrm{branch},C,F,k),
\quad (p_x,p_y)=(x_k,y_k).
\]
Advance exactly one input digit, \(i=k+1\), through this same state's branch transducer. The resulting previous pair and carry are the state entering the first symbol \(k+2\) of the S-window \([k+2,j-2)\). The finite phase key used here is
\[
(\mathrm{sector},\mathrm{branch},(x_{k+1},y_{k+1}),(c'_a,c'_b),r),
\qquad r=j-3k.
\]
This is the **own-start phase** for the next edge out of \(D(a,d)\).

## Distinction from Agent 48's 1,318 transition keys

For an edge \(D_n\to D_{n+1}\), Agent 48's phaseForTransition(source,target) starts with the **source** correction and source branch, then consumes source digits through \(k' +1\). Its returned carry/previous pair is the source-to-target transducer state entering the target word. The own-start phase above instead recomputes the **target's own** drain statistics and correction, then advances one target digit. These are different transducers and different phase meanings.

On all 9,968 existing edges, the source-to-target (branch,prev,carry) and the target's own-start (branch,prev,carry) differ on **9,740** edges (only 228 agree). The projected carry-pair sets happen to coincide:
- L: \((-2,1),(-1,0),(-1,1),(0,0)\);
- R: \((-3,1),(-2,0),(-2,1),(-1,0),(0,0)\).

That coincidence does not identify the full phases. In particular, the 1,318 transition keys must not be treated as the target state's start-phase set.

## Finite diagnostic for the own-start phase key

Across \(D_{33},\ldots,D_{10000}\):

- 9,968 states examined;
- **701** distinct own-start phase keys;
- 4,595 distinct directed edges between consecutive observed keys;
- 618 keys have multiple observed successors;
- maximum observed outdegree: **21**.

Outdegree histogram (degree: number of keys):
\[
1:83,\ 2:79,\ 3:81,\ 4:47,\ 5:24,\ 6:49,\ 7:50,\ 8:52,\ 9:41,\ 10:57,
\]
\[
11:41,\ 12:29,\ 13:13,\ 14:24,\ 15:13,\ 16:8,\ 17:6,\ 18:3,\ 21:1.
\]

First states:
| Index | Sector / branch | Previous pair | Carry | \(r\) | \(k,j\) | Window length |
|---:|---|---|---|---:|---:|---:|
| 33 | RO / R | (0,0) | (-2,1) | -1 | (6,17) | 7 |
| 34 | RE / L | (2,0) | (0,0) | -1 | (6,17) | 7 |
| 35 | LO / R | (1,1) | (-1,0) | -1 | (6,17) | 7 |
| 36 | RO / R | (1,0) | (-2,0) | 0 | (6,18) | 8 |
| 37 | RE / R | (2,2) | (-2,0) | 0 | (6,18) | 8 |

The own-start phase is still not a deterministic state on the observed orbit: 618 keys have multiple observed successors. This is finite evidence only; it does not establish an all-time transition relation or a root invariant.

## Exact integration point

In s_window_boundary_phases.js, add a separate function for the own-start phase rather than relabelling phaseForTransition:
1. use the current state's own sectorData, S-depth, branch, drain input, drainStats, and corrections;
2. call sourceCarry on that state and its own k;
3. advance the state's own digit pair at k+1 once through its own branch transducer;
4. key the resulting phase by sector, branch, previous pair, carry, and r.

Keep both phase notions in any future product: the source-to-target transducer phase proves the current output-digit correspondence, while the own-start phase initializes the next edge. The remaining closure problem still requires a source-derived weighted-drain/root-language restriction.
