# Candidate: the \(m=2,\ j\equiv9\pmod{32}\) full-forced exclusion

**Status: provisional.** The standalone arithmetic leaf and a reproduction of the previous high-sieve predicate chain compile with Lean 4.36.0-rc2. The exact source-connected module is HighM2FullForced.lean. It imports HighM1FullForced.lean, and the manual all-phase workflow has a compile step for it. The exact imported-source module still requires local dependency-closure compilation and one manual source CI acceptance run. Do not describe this as source-certified until that run passes and all axiom audits exclude sorryAx.

## Statement and inverse path

For every \(t\in\mathbb N\), set
\[
m=2,\qquad j=32t+9.
\]
The canonical high target is
\[
(x,y)=\bigl(2j+3,\ 2^{2m+2}(j+3)-(j+3m+5)\bigr)
      =(64t+21,\ 2016t+748).
\]

The full-forced normalizer takes exactly two inverse edges:
\[
(64t+21,2016t+748)
\longmapsto
(2080t+767,1008t+373)
\longmapsto
(1544t+568,1276t+469).
\]
The first edge is the even-affine inverse. The intermediate state has both coordinates odd and satisfies the odd-low gate. The terminal right coordinate is odd and at least \(469\), and
\[
2820t+1037\equiv1\pmod4
\]
is the terminal coordinate sum. The full-forced odd-image test therefore rejects the terminal state.

## Previous-sieve admission

The entire progression survives highAllowedC23WithEvenRight:

- the joint high rectangle sees \(j\equiv1\pmod4\), and its relevant \(m=2\) exception has \(j+3m+11\equiv26\pmod{32}\), not zero;
- the dyadic high check is impossible because \(2j+3\equiv5\pmod8\), whereas its right-hand side is either \(7\) or \(3\);
- the Agent19 special classes require \(j\equiv7\) or \(3\pmod8\), or \(m\ge3\);
- the Agent11 joint residues are \((j+m)\bmod4=3\) and \((j+m)\bmod16=11\);
- Agent29 and ValSix higher rectangles require \(m\ge4\), while the remaining \(m\)-only exceptional class requires \(m\equiv6\pmod{32}\);
- the Agent19Five exception requires \(m\equiv10\pmod{16}\);
- the affine-right-four normalizer does fire once, but reaches \((2080t+767,1008t+373)\), whose right coordinate is odd and therefore cannot trigger it again; that terminal right coordinate is not \(4\);
- the C58 depth tower requires \(m\ge3\), and the all-phase family is impossible because \(8\le r\) and \(r+4\le2m+2=6\);
- the C70 rectangle misses \(m\equiv2\pmod{128}\), the C23 exception requires \(j\equiv0\pmod4\), and the earlier even-right cylinder requires \(m\ge3\).

The standalone Lean predicate model proves this admission for every \(t\), rather than extrapolating from a finite scan.

## Local proof gate and acceptance status

The standalone Lean 4.36.0-rc2 proof verifies the exact two-step full-forced normalization and Boolean exclusion. A separate local Lean model proves the previous highAllowed predicate chain for every \(t\). These model checks have no sorryAx. The imported-source proof in HighM2FullForced.lean remains provisional until the manual workflow compiles it and its final axiom audit is inspected.

The workflow output is m2-full-forced.txt. No manual run has yet been dispatched in this session.

## Scope

This is a second infinite Machine C nonhalting progression, at \(m=2\), disjoint from the \(m=1\) and \(m=0\) families. It refines the necessary high parameter sieve and does not decide the remaining global existential or BB(6).
