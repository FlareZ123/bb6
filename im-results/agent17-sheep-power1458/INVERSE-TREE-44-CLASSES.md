# Seventh Sheep stratum: 44 residue classes with two-node inverse trees

**Agent 17, 20 November 2026. The 44-class subfamily is included in the accepted five-family theorem, compiled in [CI 45293408209](https://github.com/FlareZ123/bb6/actions/runs/45293408209) with Lean 4.36.0-rc2.**

This improves the single (t\equiv8\pmod{10,475,665,200}) result in [`T8-INVERSE-TREE.md`](T8-INVERSE-TREE.md). Two different first-parent types yield 44 distinct infinite residue classes, all with a two-node inverse graph.

## Accepted subfamily theorem

Define
[
T_4=10,475,665,200,qquad
T_2=31,426,995,600=3T_4.
]
The 17 (h=7,a=2) base residues are
[
R_2=\{28,64,136,244,280,352,388,568,604,676,784,892,928,1000,1036,1108,1252\}.
]
The 9 (h=7,a=4) base residues are
[
R_4=\{8,188,368,428,548,608,968,1088,1148\}.
]
Lift the latter three ways to modulus (T_2):
[
R=R_2\;\cup\;
\{r+qT_4:r\in R_4,\ q\in\{0,1,2\}\}.
]
Then (|R|=17+3\cdot9=44), with all residues distinct modulo (T_2).

The exact arithmetic certificate supports
[
\boxed{
\forall r\in R,\ \forall k\ge0,\quad
\neg\operatorname{EvenReach}
\left(10,2^{1458(r+T_2k)}\right).
}
]
The exponent period is
[
1458T_2=45,820,559,584,800,
]
so the union has density
[
\frac{44}{45,820,559,584,800}
=\frac1{1,041,376,354,200}
]
among all exponent indices.

This 44-class subfamily is now included in the compiled `SheepPower1458.noEvenReachFiveFamilies` theorem from [CI 45293408209](https://github.com/FlareZ123/bb6/actions/runs/45293408209), with transitive axiom profile `[propext, Classical.choice, Quot.sound]` and no `sorryAx`. It remains a partial exclusion, not a Sheep machine or BB(6) decision. Keep it in `im-results/`.

## Authentic source relation

For every original `EvenEdge x y`, Agent 14's `SheepEvenSourceAlgebra.even_edge_to_algebra` gives the complete alternatives:

- Generic: (y=1+3^h u), (u) odd, (x=2^a v), (a\ge1), (v\ge5) odd, and
  [
  (2^{a+1}+1)v=2^{h+1}u+3-2a.
  ]
- Exceptional: (y=1+3^h u), (u) odd, (x=3\cdot2^a), and
  [
  2^h u=3\cdot2^a+a+2.
  ]

There is no power-target hypothesis on (y), so the same source theorem applies to the intermediate affine node.

## Root classification

Every residue in (R_2) is (1 \\pmod3), every residue in (R_4) is (2 \\pmod3), and (T_2,T_4) are divisible by 3. Thus every progression has (3 \\nmid t), so LTE gives (v_3(2^{1458t}-1)=7); this justifies the complete root hidden-length range (0 \\le h \\le7).

The root is (Y_0(t)=2^{1458t}). Its complete generic low-valuation range is (0\le h\le7), with cutoffs (A_h):

| (h) | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| (A_h) | 2 | 5 | 7 | 9 | 11 | 13 | 15 | 16 |

For every (a\ge A_h), the residual
[
K_h(a)=2^{h+1}+3^h(2a-3)
]
is odd and satisfies (1<K_h(a)<2^a). The inequalities follow from the cutoff inequalities and the recurrence (K_h(a+1)=K_h(a)+2\cdot3^h). Agent 40's `SheepOddGap.no_power_signed_small_odd` excludes all these high-(a) generic sources.

The remaining 70 root congruences are checked exactly modulo (3^h(2^{a+1}+1)). For every (r\in R), there is exactly one hit:

- if (r\in R_2), the unique source has ((h,a)=(7,2));
- if (r\equiv r_0+qT_4), (r_0\in R_4), (q\in\{0,1,2\}), the unique source has ((h,a)=(7,4)).

The exceptional root sources are excluded by the special cutoff table
[
S_h=(3,5,7,9,10,12,14,16).
]
For (L_h(a)=3^h(a+2)+2^h), the cutoff satisfies (1<L_h(S_h)<2^{S_h}) and (3^h\le2^{S_h}). These bounds propagate. For (a\le1458t+h), the exceptional equation forces (2^a\mid L_h(a)), impossible; for larger (a), its right side exceeds its left side. Every smaller-(a) exceptional right side is already below (2^{1458+h}) at (t=1).

## First inverse tree: (h=7,a=2)

For the 17 residues in (R_2), the unique generic parent equation is
[
3^7(2^3+1)v+
\bigl(3^7(2\cdot2-3)+2^8\bigr)
=2^{1458t+8},
]
or
[
19,683v+2,443=2^{1458t+8}.
]
The parent is (x=4v), represented by
[
Y_2(t)=4v
=\frac{2^{1458t+10}-9,772}{19,683}.
]
For all 17 base residues, (Y_2(t)) is an even integer greater than 10 and
[
v_3(Y_2(t)-1)=0.
]
The valuation is frozen modulo (3^{10}).

The only possible hidden length at (Y_2) is therefore (h=0). Its generic predecessor equation is
[
19,683(2^{a+1}+1)w+
(39,366a-139)
=2^{1458t+11}.
]
At cutoff (A=20),
[
1<39,366\cdot20-139=787,181<2^{20},
qquad 2\cdot19,683\le2^{20}.
]
The signed-power gap excludes every (a\ge20); the 19 low-(a) modular rows have no hit for any of the 17 classes. Its exceptional-source cutoff is (S=19); the same divisibility/size argument excludes all high (a), and every low-(a) right side is below the left side already at the smallest base (t=28).

Thus (Y_2) is a terminal inverse node.

## Second inverse tree: (h=7,a=4)

For the 9 residues in (R_4), the unique generic parent equation is
[
3^7(2^5+1)v+
\bigl(3^7(2\cdot4-3)+2^8\bigr)
=2^{1458t+8},
]
or
[
72,171v+11,191=2^{1458t+8}.
]
The parent is (x=16v), represented by
[
Y_4(t)=16v
=\frac{2^{1458t+12}-179,056}{72,171}.
]
For all 9 base residues, (Y_4(t)) is an even integer greater than 10 and
[
v_3(Y_4(t)-1)=0.
]
The valuation is frozen modulo (3^9).

Its generic predecessor equation is
[
72,171(2^{a+1}+1)w+
(144,342a+285,941)
=2^{1458t+13}.
]
At cutoff (A=22),
[
1<144,342\cdot22+285,941=3,461,465<2^{22},
qquad 2\cdot72,171\le2^{22}.
]
The signed-power gap excludes every (a\ge22); the 21 low-(a) modular rows have no hit for any of the 9 classes. Its exceptional-source cutoff is (S=21), and the same divisibility/size argument excludes every exceptional parent.

Thus (Y_4) is also a terminal inverse node.

## Periods and the 44-class lift

For a generic test at a node (Y=(2^{1458t+s}+B)/C), hidden length (h), and valuation (a), the relevant modulus is
[
N=C3^h(2^{a+1}+1).
]
The certificate computes the exact multiplicative order (o_N=\operatorname{ord}_N(2)) and the exponent period (o_N/\gcd(o_N,1458)).

For the (h=7,a=2) tree:
- tree-period LCM: (6,285,399,120);
- prior 28 E-cone period LCM: (1,178,100);
- common period: (T_2=31,426,995,600);
- 89 modular rows (70 root, 19 intermediate);
- valuation moduli (3^8) and (3^{10}).

For the (h=7,a=4) tree:
- tree-period LCM: (2,095,133,040);
- prior 28 E-cone period LCM: (1,178,100);
- common period: (T_4=10,475,665,200);
- 91 modular rows (70 root, 21 intermediate);
- valuation moduli (3^8) and (3^9).

Since (T_2=3T_4), both trees are preserved by the common modulus (T_2). The certificate verifies all 180 period rows (109 distinct moduli) and all three distinct valuation moduli. It also checks the 44 base residues directly: each has exactly one root parent of the asserted type, and its intermediate node has valuation zero and no generic predecessor.

The (R_4) progressions modulo (T_4) split into three residue classes each modulo (T_2), giving 27 classes. Together with the 17 (R_2) classes this gives 44 pairwise distinct residues.

## Blank-root contradiction

Suppose (Y_0(t)=2^{1458t}) were in `EvenReach 10` for one of the 44 classes. Since (Y_0(t)>10), the existing last-edge theorem yields a genuine earlier state (x) with `EvenReach 10 x` and original `EvenEdge x Y_0(t)`. Even reachability preserves evenness, so the original source splitter applies. The complete root classification forces (x=Y_2(t)) or (x=Y_4(t)), according to the residue class. Applying the last-edge theorem to that intermediate node is impossible: both have no generic or exceptional predecessor. Hence none of the 44 classes is blank-reachable.

This is an all-time ancestry argument, not a bounded simulation.

## Nonoverlap and scope

All 44 classes are disjoint from the 28 prior E-cone progressions: each base exponent residue is different from every earlier residue, and (T_2) is a multiple of every (p/\gcd(p,1458)). They are also disjoint from the (v_3(j)=3,4,7) strata because (3\nmid t) throughout these classes, so (v_3(1458t)=6).

This is a sparse but genuine infinite family, not a solution of the seventh stratum, the Sheep machine, or BB(6). It is the current strongest candidate from this investigation.

## Verification status and next step

An independent Agent 40 BigInt audit reconstructed the exact multiplicative orders and period LCMs, and checked all 44 base classes: each has exactly its stated root parent; each intermediate node is integral, has 3-adic valuation zero after subtracting one, and has no low-valuation generic parent. The audit also checked all 180 period rows, all three valuation moduli, every generic/special cutoff inequality, and disjointness from the 28 earlier E-cones. It reproduced `Ttree2=6,285,399,120`, `Ttree4=2,095,133,040`, `Tprior=1,178,100`, `T2=31,426,995,600`, and `T4=10,475,665,200`.

The independent audit found one certificate bookkeeping error, now corrected: there are **109**, not 110, distinct moduli among the 180 period rows. The sole duplicate is `649539`, arising from the `h7a2` intermediate row `a=4` and the `h7a4` intermediate row `a=2`. This duplicate does not affect any period, LCM, or mathematical claim. The Python checker has not been executed in this environment; the independent audit used JS BigInt.

The exact JS BigInt calculations and committed Python checker support the finite modular claims. The Python checker has not been run in this environment: `python.exec` and `container.exec` returned platform `ClientError`, including trivial commands. Do not claim Lean verification.

The next action is independent review and local Lean 4.36.0-rc2 formalization against:
- `im-results/agent14-sheep-even-inverse/SheepEvenReachInverse.lean` (last-edge reachability);
- `im-results/agent14-sheep-even-inverse/SheepEvenSourceAlgebra.lean` (arbitrary-edge source split);
- `im-results/agent40-sheep-third-preimages/SheepOddGap.lean` (generic high-valuation gap).

Keep this in `im-results/` until the original-source theorem compiles and `#print axioms` shows no `sorryAx`.
