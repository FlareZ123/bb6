# Every infinite token trajectory has unbounded physical span and ones

**Status:** mathematical proof from the pinned original token clauses. The existing source proves termination of its internal token system by a two-level rank; the new deduction below is the repeated **physical left-frontier extension**, not a claim that the original rank or stack reduction is new. The signed directions have an executable constant-prefix symbolic audit. No blank-root verdict is inferred.

Source: google-deepmind/cryptids@3647718b5df22e1a61462dec0376bd204526285a, `BusyBeaver/BB6/Accelerations/M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean`.

## 1. Statement

Start from any finite token-CR point with positive head token, or any token-DR point with head 2, or token-EL point whose natural stack starts with zero and has a positive marker. Set the untouched ordinary pair tail to empty. Use explicit finite lists, retaining zero tokens at the far end. If the literal machine does not halt, then it has:

* infinitely many CR configurations whose entire physical left tape is a single 1 adjacent to the head (all farther cells zero);
* at those configurations, unbounded distance between leftmost and rightmost 1, and unbounded number of 1s;
* no repetition of a full head-relative machine configuration, including translations.

This applies to both authentic #85 and reflected #490 roots, conditional on nonhalting. In particular a nonhalting certificate based on a bounded active tape or a translated finite cycle cannot settle these roots. This is a necessary condition, not a proof of divergence. We do not assume that the displayed CR sections are consecutive or first-return sections.

## 2. Exact micro-system

Write K for the token list on physical left (nearest first) and L for the natural digit list on physical right. Token k occupies k ones followed by zero; digit a occupies a+1 ones followed by zero. CR/DR scan right at the cut x; EL scans left at x-1. DR head token is 2. The original named source clauses yield the following disjoint live rewrite rules; T and V are arbitrary tails. Prefer the special DR [1] case over generic DRsucc. In the final two EL cases, zero padding is physical blank tape.

| Input | Output | Raw moves | Cut displacement |
| --- | --- | ---: | ---: |
| EL K=[] or [0], L | CR [1], L | 1 | 0 |
| EL 0,k,T; L | CR k+1,T; L | 1 | 0 |
| EL 1,T; L | EL T; 0,L | 2 | -2 |
| EL 2,T; 0,V | EL T; 0,1,V | 7 | -3 |
| EL a+3,T; L | DR 2,a,T; L | 5 | 0 |
| DR 2,T; [] | EL T; [0,1] | 8 | -3 |
| DR 2,T; 0,V | DR 2,1,T; V | 4 | +2 |
| DR 2,T; [1] | EL 1,T; [0,0,0,1] | 28 | -1 |
| DR 2,T; a+1,V (except [1]) | CR 1,1,T; a,V | 3 | +1 |
| CR 1,T; [] | EL T; [0,1] | 9 | -2 |
| CR k+2,T; [] | EL k,T; [0,0,1] | 21 | -2 |
| CR k,T; 0,V | CR k+2,T; V | 2 | +2 |
| CR k,T; [1] | EL k,T; [0,0,0,1] | 33 | 0 |
| CR k,T; 1,0,V | CR 1,k+3,T; V | 5 | +5 |
| CR k,T; [1,1] | EL k,T; [0,0,1] | 25 | 0 |
| CR k,T; 1,1,c,V | EL k,T; 0,0,c+2,V | 25 | 0 |
| CR k,T; 1,a+2,V | DR 2,1,k,T; a,V | 15 | +5 |

CR with first digit a+2 is terminal in 2 defined moves. Here k>=1 in CR. EL starts with a zero on L and at least one positive digit later: this is preserved by every rewrite staying in EL and every bounce into EL.

The right column is a genuine signed position statement, not deduced merely from head-relative tape equality. `frontier_direction_audit.js` computes each literal direction sequence from only the forced finite prefixes of K,L in its clause, treating all unspecified cells as UNKNOWN (not blank), except beyond a known empty/singleton boundary. Every read in all 19 paths was determined; each last control state was verified. For example CR11cons has directions RRRRLLLLRRRLRRRLLLRRLLLLL, net head -1 and cut 0. The proof is finite and independent of tail length/values.

## 3. Every infinite path must repeatedly reach EL's left boundary

Here is the rank argument in explicit arithmetic form, with the termination event strengthened to an actual boundary crossing. This avoids interpreting an arbitrary existential ordinary-stack witness as a boundary crossing.

For a natural list L, let w(L)=sum L minus 1 if its last entry is positive (0 for empty). For token list K let C(K) count entries other than 1. Define S(K) by traversing K from farthest to nearest, listing the pair (number of entries behind this entry, its value) for each entry not equal to 1. The pair order is ordinary lexicographic; list lex uses a proper prefix as smaller.

A **bounce** is the deterministic sequence of CR/DR rules until the first EL or terminal. It is finite: every continuing CR/DR step decreases 2 sum L + length L. The special DR [1] rule is an EL exit. For all terminating live bounces, the following bounds hold:

* CR(k::T,L), k>=1: EL(K',L') satisfies C(K')+w(L') <= C(T)+w(L)+1, and S(K')=S(T)++ext. If equality holds in the bound and k>1, ext starts with (length T,d) for some d.
* DR(2::T,L): C(K')+w(L') <= C(T)+w(L), and S(K')=S(T)++ext.

Proof by simultaneous induction on the decreasing bounce measure. CR0 preserves w and the accumulator, and increases k. CR10 consumes weight 1, inserts exactly one non-one k+3 into the accumulator and sets k to 1. CR1high consumes at least weight 2, inserts at most one non-one (k), and switches to DR. DR0 preserves weight and inserts only a 1. DRsucc (other than singleton [1]) decreases weight by at least 1, inserts a 1 and switches to CR with head 1, so pays its possible +1. The nil/singleton/doubleton EL exits are immediate by the table: CR nil may insert a non-one k-2, CR singleton may insert k, CR [1,1] pays its insertion by w=1, CR11cons has w(c+2::V)<=w(1::1::c::V). DR exits have w=0 and add at most a 1. Every insertion is at the near end, so preserves S(T) as prefix, and CR10 inserts its first new score exactly at length T. This proves all clauses including the equality refinement.

At an EL point consider the rank
```
(C(K)+w(L), S(K), length K).
```
It is well-founded: for fixed first coordinate m, S has length <=m and entries are pairs of naturals. Bounded-length lex with proper prefixes smaller is well-founded by induction on the length bound, using the well-founded first pair and then the suffix. The last natural component handles ties.

If K=[] or [0], the next rule is a left extension, and we stop the rank argument. Otherwise:

* EL1 preserves the first two components and decreases length K.
* EL2 decreases C by 1, increases w by at most 1, and removes the final pair of S. Thus either m decreases or S is a proper prefix.
* EL0cons (K=0::k::T): compose its one move with CR0 (L=0::V), entering CR(k+3::T,V). Bounce. Initially m=1+C([k])+C(T)+w(V). The bounce bound is C(T)+w(V)+1. If k!=1 this strictly decreases m. If k=1 and m ties, the old score is S(T)++[(length T+1,0)]; the equality refinement makes the new score start S(T)++[(length T,d)], lex smaller.
* ELhigh (K=a+3::T): compose ELadd3 with DR0, entering DR(2::1::a::T,V). Bounce. Initially m=1+C(T)+w(V), output bound C([a])+C(T)+w(V). If a=1 this strictly decreases m. Otherwise, on equality the new score starts S(T)++[(length T,a)] instead of S(T)++[(length T,a+3)], lex smaller.

Thus every starting EL reaches either terminal or EL K=[]/[0] in a finite number of these deterministic chunks. Every starting CR/DR first reaches EL or terminal. After EL K=[]/[0], the one-move exit gives CR([1],L). On a nonhalting trajectory the argument applies again from there, and gives another extension after positive time. Induction gives arbitrarily many extensions. No finite simulation horizon or empirical distribution is used.

## 4. Turn the rank argument into a physical-space theorem

Define the explicit encoded lengths
```
MK(K)=sum(k+1 for k in K)
ML(L)=sum(a+2 for a in L).
B=x-MK(K); R=x+ML(L); W=R-B.
```
K may end in explicit zero tokens, so B is an **accounted** left boundary, not necessarily the actual leftmost 1. R is the end of the explicit right word, including its final separator.

The cut column in section 2 implies directly:

* Every live non-boundary rule preserves B and R.
* EL empty extends B left by 2; EL last0 extends B left by 1. R is unchanged.
* DR empty extends R right by 2; DR last1 by 5.
* CR empty head1 extends R right by 3; CR empty high by 5; CR last1 by 6; CR last11 by 1.
* No live rule contracts either accounted boundary. W is therefore nondecreasing.

For example ELhigh replaces k=a+3 by 2,a, preserving MK; cut stays fixed. CR empty high reduces MK by 2, moves cut -2, and creates ML=7; hence B unchanged and R increases5. The remaining rows are direct integer differences. No claim that W is the ordinary physical nonblank span at every step is needed.

Immediately after every left extension, K=[1], so its single one is at B+1. L is nonempty by the EL marker condition, and its last one is at R-2. These are the physical extremal ones. Their distance is W-3. Every extension increases W by at least 1, and nothing ever decreases W. Hence the distance at the jth extension is at least W_initial+j-3. Also ML<=2*(number of ones in L), since every natural digit contributes >=1 one and exactly one zero. The total one count at extensions is therefore >=1+ceil((W-2)/2). It tends to infinity.

If any full head-relative configuration repeated along a live infinite orbit, deterministic evolution and translation invariance would give an eventually periodic head-relative orbit, with bounded physical span. Contradiction. A repeated configuration on a finite halting trajectory is already impossible by determinism. Thus the recurrence excludes every normalized finite cycle (including drifting finite patterns), despite arbitrary zero padding in intermediate symbolic states.

## 5. A constructive, although very loose, bound on each frontier search

The argument also gives a controlled finite bound, not merely an abstract choice of witness. Each bounce has at most 2 sum L + length L + 1 elementary clauses, each costing <=33. It increases W by at most 6 (at most one EL boundary exit). Each EL rank descent uses at most one bounce, thus increases W by <=6 and costs <=66 W+42 defined moves. The single EL1/2 descents cost <=7. The terminal/extension cost is at most 2 after any preceding descent.

For an initial EL with mass W0 and rank first coordinate m0, encode S into m0 pairs, padding absent pairs by (0,0) and encoding each real pair (i,a) as (i+1,a+1). The rank becomes a fixed lex tuple of dimension d=2m0+2. At descent j every coordinate is <=A+6j, where A=W0+1. Define B_0(A)=A and B_d(A) by iterating the monotone function x -> B_{d-1}(x)+6 exactly A+1 times from A. A lex-decreasing controlled sequence of d coordinates has final control bound <=B_d(A): the first coordinate drops at most A times; each fixed-first-coordinate phase is bounded by the d-1 argument; add 6 to allow a separating descent. Induct on d. Thus at most (B_d(A)-A)/6 descents occur. A valid crude raw-step bound to halt or left extension is
```
( (B_d(A)-A)/6 + 1 ) * (66 B_d(A)+42) + 2
```
(with rational expression rounded upward if necessary). From CR/DR first add the initial bounce bound and start the EL estimate with its actual output or use W0+6 and m0<=W0+6. This bound is intentionally not recommended as a simulation budget: it explains why a total frontier-return algorithm exists despite astronomical possible section sizes.

## Limitations and next use

The exact literal direction audit is reproducible with Node.js. The rank and integer boundary proof are mathematical, not yet an independent Lean theorem over absolute-head trajectories. The original source has the underlying rank proof, and the new counted CR recurrence is under source CI. The conclusion rules out bounded-space avoidance, not all-time avoidance of a halting residue class. The source-certified D affine return theorem already handles arbitrary binary suffixes; the open work is arithmetic root termination, not another qualitative closure proof.
