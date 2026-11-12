# A sharp sixth/seventh image gap in the original Machine C first-return map

**Agent 4, 9 November 2026.** Original-source Lean 4.36.0-rc2 proof, [strict-image CI 42719852275](https://github.com/FlareZ123/bb6/actions/runs/42719852275) and [high-stopping CI 42720140809](https://github.com/FlareZ123/bb6/actions/runs/42720140809). 

## Theorems

Let (F=\mathrm{BB6.Agent46.secNext}) be the repository's unchanged exact accelerated first-return map for six-state two-symbol Machine C, whose genuine blank-origin section begins at ((5,1)). Let (I_n) denote the states having an incoming chain of (n) successful (F)-edges from an arbitrary source, with (I_0=\mathbb N^2). For any natural numbers (u,v) satisfying ((u+v)\bmod 4=0), define

\[
V_{u,v}=(641+1024u,\ 574+1024v).
\]

**Theorem 1 (sharp sixth/seventh image separation).** For every (u,v\in\mathbb N) with ((u+v)\bmod4=0),

\[
\boxed{V_{u,v}\in I_6\setminus I_7.}
\]

In particular, every point of this infinite two-dimensional lattice has six genuine incoming original-source transitions, and a seventh incoming transition chain is impossible from **every** potential starting section state. The natural density of this congruence-restricted lattice family in (\mathbb N^2) is exactly (1/2^{22}). 

**Theorem 2 (all-time blank exclusion).** For every (u,v,t\in\mathbb N) with ((u+v)\bmod4=0),

\[
F^t(5,1)\ne V_{u,v}
\]

whenever the (t)-fold run is defined. This includes the first six section returns; the argument has no time cutoff.

**Theorem 3 (true high-stopping consequence).** Let (j,m,k,t\in\mathbb N) satisfy the original source's necessary high-family stopping identity

\[
k+j+3m+5=2^{2m+2}(j+3).
\]

Then m ≥ 7 and membership in **any one** of the following four disjoint congruence classes is sufficient for authentic blank-root exclusion of the stopping state (2j+3,k):

| j mod 2048 | (j+3m) mod 4096 |
| ---: | ---: |
| 319 | 3517 |
| 831 | 445 |
| 1343 | 1469 |
| 1855 | 2493 |

Together these four high-stopping parameter classes have density (1/2^{21}) in the (j,m) lattice. Their overlap with stronger pre-existing stopping sieves has not been completely audited, so this parameter density is not advertised as additional integrated coverage.

Source files: [exhaustive three-parent arithmetic](../im-results/agent4-c-seven-image/CSixSeventhArithmetic.lean), [strict image theorem](../im-results/agent4-c-seven-image/CSixSeventhStrict.lean), [true blank-root exclusion](../im-results/agent4-c-seven-image/CSixSeventhRoot.lean), [original narrower high-stopping pullback](../im-results/agent4-c-seven-image/CSixSeventhGate.lean), and [four-class high-stopping pullback](../im-results/agent4-c-seven-image/CSixSeventhGateWide.lean). All source modules were compiled together in [original-source CI 42720140809](https://github.com/FlareZ123/bb6/actions/runs/42720140809), against unchanged exact section code and its proved unrestricted inverse. The workflow rejects any printed `sorryAx`; the principal theorems print ordinary Lean logical axioms only.

## Exact three-branch backward proof

The unrestricted source inverse theorem `section_preimage_all_iff` proves that **every** predecessor of (V_{u,v}), including every exceptional and unbounded recursive-bounce branch, lies among precisely the following three candidate states:

\[
\begin{aligned}
D&=(1213+1024u+1024v,\ 286+512v),\\
H_1&=(301+256u+256v,\ 739+384u+896v),\\
H_3&=(73+64u+64v,\ 850+480u+992v).
\end{aligned}
\]

The direct candidate (D) belongs to Agent 4's previously source-certified [strict fifth/sixth cylinder](2026-11-09-machine-c-new-sharp-four-five-and-five-six-cones-agent4.md) because
\[
D=(64r+61,128s+30),\quad r=18+16u+16v,\quad s=2+4v,
\]
and (r+s) is even with (s\ge2). Thus (D\in I_5\setminus I_6). The original direct section edge (D\to V_{u,v}) is genuine, proving the (I_6) inclusion.

The high parent (H_3) has its sole predecessor
\[
P_3=(921+544u+1056v,\ 424+240u+496v).
\]
Here (P_{3,2}\ge12), (P_{3,2}\equiv0\pmod8), and (P_{3,1}+P_{3,2}\equiv1\pmod8). Agent 34's source-certified two-edge exclusion therefore proves (P_3\notin I_2), hence (H_3\notin I_3).

The high parent (H_1) has at most two parents:
\[
\begin{aligned}
P_0&=(518+320u+576v,\ 627+352u+736v),\\
P_2&=(128+80u+144v,\ 819+472u+952v).
\end{aligned}
\]
The state (P_0) has odd second coordinate and coordinate sum (1\pmod4). The source odd-right image theorem forbids any incoming edge to it. The state (P_2) has the single predecessor
\[
R=(471+276u+548v,\ 644+374u+750v).
\]
Under (u+v)\bmod4=0, the state (R) has second coordinate (4\pmod8) and sum (3\pmod8), so Agent 34's two-edge exclusion proves (R\notin I_2). Therefore (P_2\notin I_3) and (H_1\notin I_4).

Any seven-edge incoming chain into (V_{u,v}) would require a six-edge incoming chain into one of (D,H_1,H_3). The three branch obstructions above exclude that possibility. The proof uses exact algebraic inverse equations and their original Lean sufficiency theorem; it requires no finite truncation of potential bounce recursion depths.

For Theorem 2, the original blank section has first seven values, at times (0,\ldots,6),

\[
(5,1),(3,4),(4,7),(20,4),(12,10),(17,11),(32,7).
\]

Each second coordinate is smaller than 574. Every later blank return has at least seven genuine predecessor edges, contradicting Theorem 1. The Lean module checks these seven actual source values and proves the all-time implication for any return time.

For Theorem 3, m ≥ 7 implies (2^{12} \mid 2^{2m+2}). Reducing the original stopping equation modulo (4096) gives (k+j+3m+5) mod 4096 = 0. The four classes above force, respectively, k mod 4096 to equal 574, 3646, 2622, or 1598. In every case the original exponential equation ensures k ≥ 574. Writing (2j+3,k) = (641+1024u,574+1024v) then yields (u+v) mod 4 = 0, exactly the hypothesis of Theorem 2. Each case has an explicit Lean arithmetic proof.

## Novelty boundary and density context

The previously documented disjoint Agent 4 union has ambient-coordinate density
\[
\frac{259}{16384}+\frac1{4194304}
=\frac{66305}{4194304}.
\]
The second s3 sixth/seventh family is disjoint from that union. It shares the first-coordinate residue (1\pmod{64}) with the first sixth/seventh family, but its parameter condition forces (u+v\equiv3\pmod4), whereas the first family requires (u+v\equiv0\pmod4); it also has first-coordinate residues different from the earlier all-depth and fourth/fifth and fifth/sixth families. For each fixed (u), exactly one residue class of (v\pmod{16}) satisfies the s3 condition. Since each coordinate is scaled by (1024), its exact ambient state-lattice density is
\[
\frac{1}{1024^2\cdot16}=\frac1{16777216}.
\]
Consequently the enlarged explicit Agent 4 union has density
\[
\frac{66305}{4194304}+\frac1{16777216}
=\boxed{\frac{265221}{16777216}}.
\]

These are explicit-density statements for unions of proven missing-image families, not censuses of all unreachable states or fractions of machines/halts resolved. There is no claim of disjointness from every result of the other 49 research agents; the exact novelty relationship to their broader image classifications remains open to comparison.

## Relevance and limits

This gives a new positive-density infinite strict (I_6\setminus I_7) family, a fully exhaustive inverse-branch argument, and two genuine-blank nonreachability consequences. The result also demonstrates how branches with recursive-bounce preimages can be controlled beyond a simple direct-lift strategy. A prior naive second lift of the fifth/sixth cone was [formally disproved by an eight-edge counterexample](../im-results/agent4-c-five-image/CAltSeventhCounterexample.lean), so the extra inverse analysis here is essential.

The original Machine C's complete stopping behavior remains open. No bound for all six-state machines, and no exact value of BB(6), follows from this single strict-image family.


## Second strict sixth/seventh image family: the s3 sector

A second, disjoint source-image family is now formally established. For all (u,v\in\mathbb N) satisfying
[
(u+v)\bmod16=(15+4u)\bmod16,
]
put
[
V(u,v)=(641+1024u,\;574+1024v).
]
The Lean theorem `exactly_six_not_seven_s3` proves that (V(u,v)) has six genuine section predecessors but no seven. The companion theorem `blank_ne_six_seven_band_s3` proves the stronger all-time statement: (V(u,v)) is not in the blank-root section orbit at any time. The proof enumerates the three exact source-parent branches; the new s3 condition places the affine parent in the first Agent 34 three-edge exclusion cone, while the other branches are excluded by the existing source theorems.

Four explicit infinite progressions inside this sector are formally proved:
[
egin{aligned}
(u,v)&=(1+16t,2),\
(u,v)&=(3+16t,8),\
(u,v)&=(16t,15),\
(u,v)&=(2+16t,5),
end{aligned}
qquad t\in\mathbb N.
]
The sector is disjoint from the earlier ((u+v)\bmod4=0) strict family: the new condition forces (u+v\equiv3\pmod4).

**Source verification.** Lean 4.36.0-rc2 CI run [43300420208](https://github.com/FlareZ123/bb6/actions/runs/43300420208) compiled `CSixSeventhStrict.lean` and `CSixSeventhRoot.lean`; the relevant declarations have no `sorryAx` dependency.

**Scope limitation.** The separate `CSixSeventhC58.lean` parameter-pullback integration did not compile in that run. In particular, the candidate high stopping progressions (j=831,;m=9770+16384t) and (j=1855,;m=12842+16384t) are not yet certified as exclusions from the exact C58 halting predicate. The strict image and all-time blank-root theorems above do not depend on that unfinished pullback.
