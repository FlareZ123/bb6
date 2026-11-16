# Inverse structure of the Machine C thin halting gateway

**Status: mathematical derivation for review; not yet Lean-formalized.** This note is an attempt to connect the exact three-counter gateway in `BB6CLine` to the first/second stopping loci studied by Agents 15 and 47. It is not a Machine C nonhalting proof.

Let
[
T_j=(0,2j,4j+10).
]
The relevant exact cases of `BB6CLine.nextC` are:

- for (c\ge4,a\ge1): ((a+1,k,c)\mapsto(a,k+1,c-1));
- for (c=0,a\ge2): ((a+2,k,0)\mapsto(a,1,2k+1));
- for (c\ge4,a=0,k\) even: ((0,k,c)\mapsto(2k+2,2,c-3)).

The remaining special cases are those in `im-results/agent11-c-line/CLine.lean`.

## First inverse branch

For (j\ge1), repeated inversion of the first rule gives the chain
[
(0,2j,4j+10)
\leftarrow (1,2j-1,4j+11)
\leftarrow\cdots\leftarrow
(2j-1,1,6j+9).
]

At the final (k=1) state ((2j-1,1,6j+9)), there are two relevant predecessor possibilities:

1. the first-rule predecessor ((2j,0,6j+10)), which has no predecessor under any case of `nextC`;
2. the (c=0) predecessor
   [
   Q_j=(2j+1,3j+4,0),
   ]
   because (2(3j+4)+1=6j+9).

Thus if the backward path does not branch earlier through the even-(k), (a=0) rule, reachability of (T_j) forces reachability of the CLine (c=0) state (Q_j). For odd (j), there is no earlier (k=2) branch, so this is the only viable predecessor route. For (j=0), (T_0=(0,0,10)) is predecessorless.

## Additional inverse branch for even (j)

If (j) is even, the chain also reaches
[
(2j-2,2,6j+8).
]
This state has an alternative predecessor under the third rule:
[
U_0=(0,K_0,C_0)=(0,j-2,6j+11).
]

More generally, from an (a=0) state (U_r=(0,K_r,C_r)), the same inverse branch is available whenever (K_r\ge4) and (K_r\equiv0\pmod4), and gives
[
K_{r+1}=\frac{K_r-4}{2},\qquad C_{r+1}=C_r+K_r+1.
]
Starting from (K_0=j-2, C_0=6j+11), the closed forms are
[
K_r+4=\frac{j+2}{2^r},\qquad
C_r=8j+15-2\frac{j+2}{2^r}-3r.
]

At every odd depth (r=2m-1), (C_r) is even. If (K_r\ge2), the (k=1) point on the decrement chain from (U_r) has a (c=0) predecessor
[
Q_r=(K_r+1,\frac{C_r+K_r-2}{2},0).
]
Put
[
j'=\frac{j+2}{2^{2m}}-3.
]
Then (K_r+1=2j'+3), and the second coordinate (k) of (Q_r) satisfies exactly
[
k+j'+3m+5=2^{2m+2}(j'+3).
]
This is the same Diophantine equation used in Agent 47's second stopping-family results. If the (k=2) inverse branch is continued instead of taking the (c=0) predecessor, the recurrence strictly decreases (K_r); terminal (K_r=0), or a parity mismatch at an even depth, gives a predecessorless branch.

## Consequence and relation to existing work

The inverse tree therefore suggests the following necessary condition:
[
\operatorname{Reach}(T_j)
\Longrightarrow
\operatorname{Reach}(Q_j)
\quad\text{or}\quad
\exists m\ge1,j',k,\;
j+2=2^{2m}(j'+3),\;
k+j'+3m+5=2^{2m+2}(j'+3),\;
\operatorname{Reach}(2j'+3,k,0).
]

The second disjunct is precisely an Agent 47 second-stop equation state. The first disjunct is a CLine (c=0) predecessor family ((2j+1,3j+4,0)); it should not be silently identified with Agent 15's separate `CReach 1 k` first-family representation without a proved source-coordinate bridge.

The (j=1) first-family point is ((3,7,0)), which Agent 15 already excludes by `source_no_3_7`. Other first- and second-family parameters remain. Agent 15's `blank_halt_requires_residual_families` is already a source-level reduction of a raw blank-root halt to its own exact first/second families, and should be treated as the stronger established root reduction until this CLine inverse tree is checked and connected formally.

The reproducible script [m32_check.js](m32_check.js) independently implements the B8/M32 quotient BFS and asserts the documented counts (31,570 reachable quotient states and 189,834 representative edges). It excludes the projected (j=1) point ((3,7,0)), but allows many other projected first/second-family points; that finite computation alone does not close the gateway.

## What would make this a theorem

A Lean proof should classify **all** predecessors of the displayed chain states, including both the (c=0) and (a=0) alternatives, prove the (K_r,C_r) recurrence and its parity/termination cases, then connect the resulting first/second CLine families to existing source-certified exclusions. No bounded forward scan is a substitute for this inverse completeness argument.
