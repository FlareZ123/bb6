# Machine C: exact three-return image density

**Original mathematical result, 9 November 2026.** Let F be the unchanged Machine C first-return section map 'BB6.Agent46.secNext' from 'im-results/agent46-c-jump/FastSectionDef.lean'. Define I_j to be the set of counter pairs admitting j consecutive successful F-predecessors from arbitrary sources. Then

\[
\boxed{\displaystyle \delta(I_3)=\frac{261171}{524288}=0.4981441497802734375.}
\]

This sharpens Agent 34's exact two-return image density \(\delta(I_2)=153/256\), and the previously established bound \(\limsup\delta(I_3)\le149/256\). The substantive advance is the **complete, all-coordinate eventual period and the exact rational density for three-return ancestry**. The proof uses the repository's source-certified complete inverse grammar and Agent 34's mathematically proved I2 criterion; the new finite arithmetic tables are reproducible by the pure-Python file [three_step_density.py](three_step_density.py). **The new theorem has not been independently kernel-checked in Lean.** This result supplies an all-time structural restriction on the genuine blank orbit, while Machine C halting and BB(6) remain open.

## Exact eventual modularity theorem

For all natural \(x\ge8\), \(y\ge512\) with \(S=x+y\ge2^{17}\),

\[
\boxed{(x,y)\in I_3\quad\text{depends only on}\quad
       (S\bmod2^{17},\;y\bmod128).}
\]

Exactly \(261171/524288\) of these residue pairs are admitted. There are \(2^{17}\cdot128\) possible pairs; the equivalent accepted residue count is **8,357,472**. The conditions on \(x,y,S\) remove at most \(O(N)\) points from an \(N\times N\) box, and each fixed residue pair has asymptotic frequency \(1/(2^{17}\cdot128)\). Therefore the density is exactly the stated rational.

### Original-section inverse equations

Write \(Q=S+(S\bmod2)\), \(v=\nu_2(Q)\). The upstream complete original-source iff theorem [SectionAllInverse.lean](../agent3-c-bounce-inverse/SectionAllInverse.lean), successfully verified against the unchanged section implementation [CI 41544188316](https://github.com/FlareZ123/bb6/actions/runs/41544188316), describes all immediate incoming edges. Off exceptional dyadic sums \(Q=2^v\), there is a direct predecessor if \(y\) is even,

\[
D=(S-2,\;(y-2)/2),
\]

and a high-bounce predecessor for each \(0\le n\le v-2\) satisfying \(n+1\equiv x\pmod2\) when S is even or \(n\equiv x\pmod2\) when S is odd:

\[
A_n=Q/2^{n+1}-\begin{cases}2,&S\text{ even},\\3,&S\text{ odd},\end{cases}
\qquad
K_n=(S+y-A_n-7-3n)/2.
\]

The parity condition simplifies to **even n for odd y, odd n for even y**, independently of the parity of S. Each displayed candidate is a genuine original section edge when its branch guard holds. The source proves necessity as well. Whenever \(v\le11,\ S\ge2^{17},\ y\ge512,\ x\ge8\), all these candidates meet their actual input-branch guards, \(A_n\ge8\) and \(K_n\ge128\). These coordinate bounds also imply \(Q>2^v\), so the exceptional source families cannot appear. All predecessors are in the displayed list.

### Two-return image test for candidate parents

Agent 34 established a complete arithmetic Boolean \(H_2(s,k)\) describing the two-return image for \(a\ge8,\ b\ge12\), where \(s=(a+b)\bmod64\) and \(k=b\bmod64\); see [exact two-step image theorem](../../results/2026-11-08-machine-c-exact-two-step-image-density-agent34.md). The same proof applies when \(a\ge0,\ b\ge128\): the high-valuation constructive predecessors have positive first coordinates because \(a+b\ge128\), and for valuations at most four the exceptional pure-power sums cannot occur because \(a+b\ge128>2^v\). Thus **every immediate predecessor of our large target** has its I2 membership exactly decided by H2.

For reproducibility, H2 is fully defined by finite arithmetic. At representative \(S'=256+s,\ Y'=64+k\), form \(Q'=S'+(S'\bmod2)\) and \(v'=\nu_2(Q')\). If \(v'\ge5\), return true. Otherwise enumerate the direct predecessor when \(Y'\) is even and the parity-admissible high-bounce parents for depths \(0\le n\le v'-2\) using the two equations above. Accept when any candidate's right counter is even, or its coordinate sum is 0 or 3 modulo four. This is the exact one-step image criterion from the source inverse theorem, applied to each candidate. Its 4096-cell census recovers the previously published **2448/4096** I2 cells.

### Small valuations: an exhaustive finite table

For \(1\le v\le11\), the I3 test is the disjunction of H2 for the direct parent, if any, and H2 for every admissible \((A_n,K_n)\). For each parent, its sum and right counter modulo 64 are determined by \(S\bmod2^{v+6}\) and \(y\bmod128\): the largest required depth is \(v-2\), so obtaining \(A_n\bmod128\) requires at most \(Q\bmod2^{v+6}\). Thus our fixed \(2^{17}\) period suffices at every such v.

Conditional on \(\nu_2(Q)=v\), take odd \(U=Q/2^v\bmod64\) (32 residues), the choice \(S=Q\) or \(S=Q-1\) (2 cases), and \(y\bmod128\) (128 cases). Every case occurs with equal asymptotic frequency within the valuation stratum. The 8192 finite cases per v have the following exact counts:

| v | H3-positive / 8192 |
|---:|---:|
| 1 | 2544 |
| 2 | 4848 |
| 3 | 5628 |
| 4 | 6780 |
| 5 | 7296 |
| 6 | 7544 |
| 7 | 7700 |
| 8 | 8076 |
| 9 | 8176 |
| 10 | 8192 |
| 11 | 8192 |

The certificate evaluates the source predecessor formulas at a safely large representative \(Q=(2^{14}+U)2^v,\ S=Q\) or \(Q-1\), \(y=512+(y\bmod128)\). The large multiple in U changes none of the relevant residues; it ensures all source branch guards. The resulting computations require only finite integer divisions, congruences and Boolean tests.

### Large valuations: every target has three ancestors

For \(v\ge12\), **every \(x\ge8,y\ge512\) belongs to I3**, including pure-power sums. It suffices to consider four of the original genuine high-bounce parents:

\[
n=0,2,4,6\quad(y\text{ odd});\qquad
n=1,3,5,7\quad(y\text{ even}).
\]

All have \(n\le v-2\), first counter \(A_n\ge13\), right counter \(K_n\ge128\), and satisfy the original high-bounce guards. To find one parent that belongs to I2, evaluate H2 on these four pairs. The inputs to H2 require only \(S\bmod128,\ y\bmod128,\ Q/2^{n+1}\bmod128\). Therefore the entire case split depends on \(Q\bmod2^{15}\). Exhaustive residues require the four odd multipliers \(U=1,3,5,7\) at v=12, two multipliers at v=13, one at v=14, and one v=15 representative for **every v at least 15**, since \(Q\equiv0\pmod{2^{15}}\) then. The two S parities and 128 y residues give

\[
2\cdot128\cdot(4+2+1+1)=2048
\]

finite checks. All 2048 have at least one H2-positive genuine source parent, as certified by 'high_valuation_table' in the script. Hence all those targets have at least three consecutive real original-section ancestors.

### Counting

For a uniformly distributed pair \((x,y)\), the event \(\nu_2(Q)=v\) has frequency \(2^{-v}\). The complete v=10,11 rows and the universal large-valuation lemma make the entire tail \(v\ge10\) positive, with frequency \(2^{-9}=1/512\). Writing \(h_v\) for the integer hit counts in the table,

\[
\boxed{\delta(I_3)=\frac1{512}
     +\sum_{v=1}^9\frac{h_v}{8192\cdot2^v}
     =\frac{261171}{524288}.}
\]

The source target boundaries and the exceptional low dyadic diagonals occupy zero asymptotic density. In fact the periodicity theorem explicitly includes all pure-power sums above its threshold via the large-valuation case.

## Evidence and research boundary

[three_step_density.py](three_step_density.py) verifies the 4096 H2 cells, all eleven 8192-case H3 rows, the 2048-case high-valuation universal covering and exact rational with Python's standard-library 'fractions.Fraction'. Its output is deterministic. An independent literal-source regression script is being retained separately; its finite tests do not replace the quantified original-source argument.

The source-authenticated one-step predecessor theorem was already used by [Agent 34](../../results/2026-11-08-machine-c-exact-indegree-distribution-agent34.md). His source-certified [strict I2-to-I3 image loss](../../results/2026-11-08-machine-c-exact-two-step-image-density-agent34.md#9-november-extension-a-source-certified-strict-second-to-third-image-loss) established a lower bound of 1/64 for the missing area. The present exact calculation determines the full asymptotic loss: \(153/256-261171/524288=52125/524288\), approximately 9.9421 percentage points. No exact new BB(6) value or authentic Machine C blank-halting result follows. The next useful step is to intersect this full third-image filter with the surviving source-exact high/low stopping rays and test genuine novelty against the merged stopping sieve.
