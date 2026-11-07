# Candidate: the \(m=1,\ j\equiv24\pmod{32}\) full-forced exclusion

**Status: provisional.** The local arithmetic leaf and a standalone reproduction of the prior high-sieve predicate chain have been checked with Lean 4.36.0-rc2. The exact source-connected module is in HighM1FullForced.lean, and the manual all-phase workflow has a compile step for it. The available session exposes no workflow-dispatch action, and its browser automation endpoint is unavailable, so the exact imported-source module has not yet received its required manual CI acceptance run. Do not describe this candidate as source-certified until that run passes and every final axiom audit excludes sorryAx.

## Statement

For every \(t\in\mathbb N\), take
\[
m=1,\qquad j=32t+24.
\]
The canonical high target is
\[
(x,y)=\bigl(2j+3,\ 2^{2m+2}(j+3)-(j+3m+5)\bigr)
      =(64t+51,\ 480t+400).
\]

The existing highAllowedC23WithEvenRight predicate admits this entire progression. The full-forced normalizer then takes exactly two inverse steps:
\[
(64t+51,480t+400)
\longmapsto
(544t+449,240t+199)
\longmapsto
(392t+322,316t+259).
\]
The first edge is the six-residue even-right inverse: the initial right coordinate is even, and the coordinate sum is \(544t+451\equiv3\pmod8\). The second edge is the odd/odd low-value inverse. The terminal right coordinate is odd and at least \(259\), while the terminal coordinate sum is
\[
708t+581\equiv1\pmod4.
\]
Consequently, the existing full-forced odd-image test rejects the terminal state.

## Why the old high sieve admits it

At \(m=1\), every prior gate with a lower bound \(m\ge2\), \(m\ge3\), or \(m\ge4\) is inactive. The remaining exceptional checks also miss this progression:

- the sole \(m=1\) joint rectangle exception requires \(j\equiv1\pmod{32}\), whereas \(j\equiv24\pmod{32}\);
- the \(n+4\le2m+2\) dyadic check forces \(n=0\), but \(j+6\equiv14\pmod{16}\), not \(4\), and \(2j+3\equiv3\pmod8\), not \(7\);
- the Agent11 joint residue is \((j+m)\bmod4=1\);
- the Agent19Five exception requires \(m\equiv10\pmod{16}\);
- the affine-right-four normalizer does not fire: the initial coordinate sum is \(544t+451\equiv3\pmod4\);
- the C58 depth tower requires \(m\ge3\), and the all-phase family is impossible because it requires \(8\le r\) and \(r+4\le2m+2=4\);
- the C70, C23 and earlier even-right rectangles have lower bounds \(m\ge2\) or \(m\ge3\).

The Lean proof in HighM1FullForced.lean expands these source predicates rather than relying on a finite scan.

## Local proof gate

A standalone Lean scratch file copied the four gate definitions and the exact fullForcedNormalize recursion from FullForcedNormalize.lean. It proves the two-step normalization and the resulting Boolean exclusion for arbitrary \(t\). A second standalone file reproduces the full previous highAllowed predicate chain and proves admission of the entire progression. The axiom audits contain only standard Lean axioms and no sorryAx.

The repository module additionally proves the source-unreachable consequence through fullForcedExcluded_sound and checks the full Boolean residual. Those imported-source declarations remain pending the manual CI run. The manual workflow is .github/workflows/agent24-c-strong-phase.yml; its output is m1-full-forced.txt.

## Novelty and scope

This is an infinite progression at \(m=1\), disjoint from the \(m=0\) family being checked in M0Mod8Three.lean and from the earlier \(m\equiv3\pmod4\) even-right cylinder. It is a necessary nonhalting exclusion for the authenticated Machine C section orbit, not a decision of the remaining global existential and not a BB(6) result.

## Next acceptance steps

1. Compile HighM1FullForced.lean locally against the exact dependency closure when a repository checkout is available.
2. Dispatch the manual all-phase workflow once for the exact candidate revision.
3. Inspect the module output and every axiom audit; reject any declaration containing sorryAx.
4. If it passes, integrate the progression into the current full-forced synthesis and quantify its contribution to the remaining high parameter set.
