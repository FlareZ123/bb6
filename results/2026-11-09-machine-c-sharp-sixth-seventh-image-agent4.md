# A sharp sixth/seventh image gap in the original Machine C first-return map

**Agent 4, 9 November 2026.** Original-source Lean 4.36.0-rc2 proof, [CI 42718081992](https://github.com/FlareZ123/bb6/actions/runs/42718081992). 

## Theorems

Let (F=\mathrm{BB6.Agent46.secNext}) be the repository's unchanged exact accelerated first-return map for six-state two-symbol Machine C, whose genuine blank-origin section begins at ((5,1)). Let (I_n) denote the states having an incoming chain of (n) successful (F)-edges from an arbitrary source, with (I_0=\mathbb N^2). For arbitrary natural numbers (u,v), define

\[
V_{u,v}=(641+4096u,\ 574+16384v).
\]

**Theorem 1 (sharp sixth/seventh image separation).** For every (u,v\in\mathbb N),

\[
\boxed{V_{u,v}\in I_6\setminus I_7.}
\]

In particular, every point of this infinite two-dimensional lattice has six genuine incoming original-source transitions, and a seventh incoming transition chain is impossible from **every** potential starting section state. The natural density of this specific lattice in (\mathbb N^2) is exactly (1/2^{26}). 

**Theorem 2 (all-time blank exclusion).** For every (u,v,t\in\mathbb N),

\[
F^t(5,1)\ne V_{u,v}
\]

whenever the (t)-fold run is defined. This includes the first six section returns; the argument has no time cutoff.

**Theorem 3 (true high-stopping consequence).** Let (j,m,k,t\in\mathbb N) satisfy the original source's necessary high-family stopping identity

\[
k+j+3m+5=2^{2m+2}(j+3).
\]

Then

\[
m\ge7,\quad j\equiv319\pmod{2048},
\quad j+3m\equiv15805\pmod{16384}
\]

imply that the authentic blank-origin section at time (t) is different from ((2j+3,k)). This removes an infinite lattice of high-stopping parameter pairs, of density (1/2^{25}) in (\mathbb N^2) viewed solely as the ((j,m)) coordinate lattice. It is a genuine all-time stopping-gate exclusion. It may overlap stronger independently established composite sieves; no net increase to the current integrated high-sieve density is asserted.

Source files: [exhaustive three-parent arithmetic](../im-results/agent4-c-seven-image/CSixSeventhArithmetic.lean), [strict image theorem](../im-results/agent4-c-seven-image/CSixSeventhStrict.lean), [true blank-root exclusion](../im-results/agent4-c-seven-image/CSixSeventhRoot.lean), [high-stopping pullback](../im-results/agent4-c-seven-image/CSixSeventhGate.lean). All four were compiled together in [original-source CI 42718081992](https://github.com/FlareZ123/bb6/actions/runs/42718081992), against unchanged exact section code and its proved unrestricted inverse. The workflow rejects any printed `sorryAx`; the principal theorems print ordinary Lean logical axioms only.

## Exact three-branch backward proof

The unrestricted source inverse theorem `section_preimage_all_iff` proves that **every** predecessor of (V_{u,v}), including every exceptional and unbounded recursive-bounce branch, lies among precisely the following three candidate states:

\[
\begin{aligned}
D&=(1213+4096u+16384v,\ 286+8192v),\\
H_1&=(301+1024u+4096v,\ 739+1536u+14336v),\\
H_3&=(73+256u+1024v,\ 850+1920u+15872v).
\end{aligned}
\]

The direct candidate (D) belongs to Agent 4's previously source-certified [strict fifth/sixth cylinder](2026-11-09-machine-c-new-sharp-four-five-and-five-six-cones-agent4.md) because
\[
D=(64r+61,128s+30),\quad r=18+64u+256v,\quad s=2+64v,
\]
and (r+s) is even with (s\ge2). Thus (D\in I_5\setminus I_6). The original direct section edge (D\to V_{u,v}) is genuine, proving the (I_6) inclusion.

The high parent (H_3) has its sole predecessor
\[
P_3=(921+2176u+16896v,\ 424+960u+7936v).
\]
Here (P_{3,2}\ge12), (P_{3,2}\equiv0\pmod8), and (P_{3,1}+P_{3,2}\equiv1\pmod8). Agent 34's source-certified two-edge exclusion therefore proves (P_3\notin I_2), hence (H_3\notin I_3).

The high parent (H_1) has at most two parents:
\[
\begin{aligned}
P_0&=(518+1280u+9216v,\ 627+1408u+11776v),\\
P_2&=(128+320u+2304v,\ 819+1888u+15232v).
\end{aligned}
\]
The state (P_0) has odd second coordinate and coordinate sum (1\pmod4). The source odd-right image theorem forbids any incoming edge to it. The state (P_2) has the single predecessor
\[
R=(471+1104u+8768v,\ 644+1496u+12000v).
\]
The state (R) has second coordinate (4\pmod8) and sum (3\pmod8), so Agent 34's two-edge exclusion proves (R\notin I_2). Therefore (P_2\notin I_3) and (H_1\notin I_4).

Any seven-edge incoming chain into (V_{u,v}) would require a six-edge incoming chain into one of (D,H_1,H_3). The three branch obstructions above exclude that possibility. The proof uses exact algebraic inverse equations and their original Lean sufficiency theorem; it requires no finite truncation of potential bounce recursion depths.

For Theorem 2, the original blank section has first seven values, at times (0,\ldots,6),

\[
(5,1),(3,4),(4,7),(20,4),(12,10),(17,11),(32,7).
\]

Each second coordinate is smaller than 574. Every later blank return has at least seven genuine predecessor edges, contradicting Theorem 1. The Lean module checks these seven actual source values and proves the all-time implication for any return time.

For Theorem 3, (m\ge7) implies (2^{14}\mid 2^{2m+2}). Reducing the stopping equation modulo (2^{14}=16384) gives (k\equiv574\pmod{16384}); an explicit exponential lower bound establishes (k\ge574). The condition (j\equiv319\pmod{2048}) gives (2j+3=641+4096u). Therefore ((2j+3,k)=V_{u,v}) for natural (u,v), and Theorem 2 applies.

## Novelty boundary and density context

The earlier [Agent 4 strict all-depth hierarchy](2026-11-09-machine-c-all-depth-strict-section-image-hierarchy-agent4.md) consists of first coordinates (3\pmod4). Its combined density is (1/64). The later source-proven fourth/fifth and fifth/sixth cones have first coordinates (25\pmod{64}) and (61\pmod{64}), respectively. The new sixth/seventh cone has first coordinate (1\pmod{64}); these three **explicit Agent 4 families** are pairwise disjoint. Their combined ambient-coordinate density is therefore

\[
\frac{259}{16384}+\frac1{67108864}
=\boxed{\frac{1060865}{67108864}}.
\]

This is an explicit-density statement for a union of proven missing-image families, rather than a census of all unreachable states. There is no claim of disjointness from every result of the other 49 research agents. The sixth/seventh certificate is new within the present explicit Agent 4 source-image construction; the exact novelty relationship to other agents' broader image classifications remains open to comparison.

## Relevance and limits

This gives a new positive-density infinite strict (I_6\setminus I_7) family, a fully exhaustive inverse-branch argument, and two genuine-blank nonreachability consequences. The result also demonstrates how branches with recursive-bounce preimages can be controlled beyond a simple direct-lift strategy. A prior naive second lift of the fifth/sixth cone was [formally disproved by an eight-edge counterexample](../im-results/agent4-c-five-image/CAltSeventhCounterexample.lean), so the extra inverse analysis here is essential.

The original Machine C's complete stopping behavior remains open. No bound for all six-state machines, and no exact value of BB(6), follows from this single strict-image family.
