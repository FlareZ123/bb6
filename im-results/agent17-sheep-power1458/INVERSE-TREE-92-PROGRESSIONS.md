# Seventh Sheep stratum: 93 inverse-tree progressions

**Agent 17's 20 November candidate, independently audited and extended by Agent 40 on 21 November 2026. Original-source Lean formalization pending.**

The 44-class two-node result in [`INVERSE-TREE-44-CLASSES.md`](INVERSE-TREE-44-CLASSES.md) and the two families below are joined by the earlier mixed-parent class (t≡1 mod T_0) in [`INVERSE-TREE-PROGRESSION.md`](INVERSE-TREE-PROGRESSION.md). There are five disjoint families of root exponents (2^{1458t}), with 75 base residue classes across five periods. Since (T_2=3T_4), the (h=7,a=4) nine classes lift to 27 classes modulo (T_2); in that presentation the total is 93 progression classes. The filename is retained for compatibility with existing links.

## Five family theorem

For each row below, every listed base residue (r) and every (k\ge0) gives a blank-root-unreachable target
[
\neg\operatorname{EvenReach}(10,2^{1458(r+Tk)}).
]

| First parent | Base residues | Period (T) | Inverse graph |
|---|---:|---:|---:|
| (t=1 mod T_0) | 1 | (32,526,940,446,000) | 15 nodes, 14 edges (six leaves) |
| (h=1,a=3) | 26 | (80,313,433,200) | 7 nodes, 6 edges |
| (h=3,a=6) | 22 | (150,151,201,200) | 3 nodes, 2 edges |
| (h=7,a=2) | 17 | (31,426,995,600) | 2 nodes, 1 edge |
| (h=7,a=4) | 9 | (10,475,665,200) | 2 nodes, 1 edge |

All 75 base residues are distinct modulo 1260, and all five periods are multiples of 1260. Thus the five progression families are pairwise disjoint. Each is also disjoint from the 28 earlier E-cone progressions.

The combined density among all exponent indices is
[
\delta=
\frac{1}{1458T_0}
+\frac{26}{1458T_1}
+\frac{22}{1458T_3}
+\frac{17}{1458T_2}
+\frac{9}{1458T_4}
=\frac{2615983}{2039244004321524000}.
]
The 44-class subfamily from the preceding report is (17+3\cdot9=44) classes modulo (T_2=3T_4). Adding the mixed-parent (t=1 mod T_0) class and the 26 (h=1,a=3) and 22 (h=3,a=6) classes gives 93 classes in the combined presentation.

## Residue sets

The added mixed-parent family has (R_0=\\{1\\}) and (T_0=32,526,940,446,000=2^4\\cdot3^7\\cdot5^3\\cdot7\\cdot11\\cdot13\\cdot17\\cdot19\\cdot23). Its exact 15-node graph and cutoff tables are given in [`INVERSE-TREE-PROGRESSION.md`](INVERSE-TREE-PROGRESSION.md).

[
egin{aligned}
R_1={}&\{50,58,170,178,230,238,350,430,490,598,610,710,\
&770,778,790,850,890,898,958,1030,1070,1078,1130,1138,1210,1250\},
\[2mm]
R_3={}&\{40,124,152,236,292,320,376,404,544,572,628,656,740,796,824,880,992,1048,1076,1132,1160,1244\},
\[2mm]
R_2={}&\{28,64,136,244,280,352,388,568,604,676,784,892,928,1000,1036,1108,1252\},
\[2mm]
R_4={}&\{8,188,368,428,548,608,968,1088,1148\}.
end{aligned}
]
The (R_0,R_1,R_3,R_2,R_4) periods are respectively (T_0,T_1,T_3,T_2,T_4). For the combined 93-class presentation modulo (T_2), replace (R_4) by
[
\{r+qT_4:r\in R_4,\ q\in\{0,1,2\}\}.
]

## Finite inverse graphs

All affine nodes have the form
[
Y(t)=\frac{2^{1458t+s}+B}{C},
]
with (B\le0). Every non-root node in these four families has (v_3(Y(t)-1)=0), so only hidden length (h=0) is possible at those nodes.

### (h=1,a=3): seven-node tree

The root has the unique parent
[
Y_1(t)=\frac{2^{1458t+5}-104}{51}.
]
The full graph is
[
Y_0\xrightarrow{(1,3)}Y_1,
\quad
Y_1\xrightarrow{(0,1)}Y_2,
\quad
Y_1\xrightarrow{(0,2)}Y_3,
\quad
Y_3\xrightarrow{(0,1)}Y_4
\xrightarrow{(0,2)}Y_5
\xrightarrow{(0,2)}Y_6.
]
The affine nodes are:
[
\begin{array}{c|r|r|r}
i&s&B&C\\\hline
1&5&-104&51\\
2&7&-518&255\\
3&8&-1444&459\\
4&10&-6694&2295\\
5&13&-81092&20655\\
6&16&-896596&185895
\end{array}
]
Nodes (Y_2) and (Y_6) are leaves. The generic cutoffs (A) at nodes 1–6 are (11,13,14,17,20,24); exceptional cutoffs (S) are (10,13,14,16,20,23). The 26 base residues in (R_1) have exactly the displayed root and intermediate edges, with no others below the cutoffs.

### (h=3,a=6): three-node chain

The unique root parent is
[
Y_1(t)=\frac{2^{1458t+10}-16576}{3483}.
]
The graph is
[
Y_0\xrightarrow{(3,6)}Y_1
\xrightarrow{(0,2)}Y_2,
\qquad
Y_2(t)=\frac{2^{1458t+13}-174404}{31347}.
]
The final node (Y_2) is a leaf. Generic cutoffs at (Y_1,Y_2) are (18,21); exceptional cutoffs are (17,20). All 22 residues in (R_3) have exactly this graph.

### (h=7,a=2): two-node chain

[
Y_0\xrightarrow{(7,2)}Y_1,
\qquad
Y_1(t)=\frac{2^{1458t+10}-9772}{19683}.
]
The second node is a leaf. Its generic and exceptional cutoffs are (20,19).

### (h=7,a=4): two-node chain

[
Y_0\xrightarrow{(7,4)}Y_1,
\qquad
Y_1(t)=\frac{2^{1458t+12}-179056}{72171}.
]
The second node is a leaf. Its generic and exceptional cutoffs are (22,21).

## Why each inverse graph proves non-reachability

For every original even edge, Agent 14's `SheepEvenSourceAlgebra.even_edge_to_algebra` gives the generic and exceptional source equations. Agent 14's `blank_even_inverse_cases` packages these equations for affine power targets (dY+c=2^n). It applies uniformly: root (d=1,c=0); intermediate (Y=(2^{j+s}+B)/C) uses (d=C,c=-B). All offsets are nonpositive.

Suppose a root target were in `EvenReach 10`. The last-edge theorem yields a genuine predecessor with even reachability. The original source splitter forces one of the graph's listed incoming edges. Repeating this down the finite inverse graph eventually reaches a leaf. Each leaf has no generic predecessor below its cutoff and no exceptional predecessor, a contradiction.

The high-(a) generic cases are uniformly excluded by `SheepOddGap.no_power_signed_small_odd`. At each cutoff (A), the residual (K(a)) is odd and satisfies (1<K(A)<2^A), with slope (2D\le2^A), so these inequalities persist for all (a\ge A).

Exceptional sources are handled using
[
2^{1458t+s+h}=3D\,2^a+L(a),
\qquad L(a)=D(a+2)+2^h(C-B).
]
At each special cutoff (S), (1<L(S)<2^S) and (D\le2^S). For (a\le1458t+s+h), the equation forces (2^a\mid L(a)), impossible; for larger (a), the right side exceeds the left side. All smaller (a<S) are checked at the minimum base (t), where the right side is already smaller; the left side increases with (t).

## Exact periods and reproducibility

For a generic test at node (Y=(2^{1458t+s}+B)/C), hidden length (h), and valuation (a), the modulus is
[
N=C3^h(2^{a+1}+1).
]
The checker computes the exact multiplicative order of 2 modulo (N) and the exponent period (o_N/\gcd(o_N,1458)), together with valuation-freezing moduli.

| Family | Tree-period LCM | Prior-period LCM | Final (T) | Modular rows |
|---|---:|---:|---:|---:|
| (t=1 mod T_0) | 32,526,940,446,000 | 1,178,100 | 32,526,940,446,000 | 455 |
| (h=1,a=3) | 80,313,433,200 | 1,178,100 | 80,313,433,200 | 163 |
| (h=3,a=6) | 30,030,240,240 | 1,178,100 | 150,151,201,200 | 107 |
| (h=7,a=2) | 6,285,399,120 | 1,178,100 | 31,426,995,600 | 89 |
| (h=7,a=4) | 2,095,133,040 | 1,178,100 | 10,475,665,200 | 91 |

The new checker is [`inverse_tree_h1a3_h3a6_certificate.py`](inverse_tree_h1a3_h3a6_certificate.py). The (h=7) families are checked by [`inverse_tree_44_classes_certificate.py`](inverse_tree_44_classes_certificate.py). The latter verifies 180 order-period rows across 109 distinct moduli and three distinct valuation moduli. The new checker verifies each graph at all 48 base residues and computes the corresponding exact periods.

All 75 base residues are pairwise distinct modulo 1260. Every base residue is nonzero modulo 3, while all five periods are divisible by 3; hence every progression keeps 3∤t and LTE gives v₃(2^(1458t)−1)=7. This justifies the root hidden-length bound h≤7 used in every tree. All five periods are multiples of 1260, and each base residue is disjoint from every old E-cone class. Thus the five families are mutually disjoint and do not overlap the 28 prior progressions.

## Independent exact-arithmetic audit

Agent 40 independently reconstructed all five inverse graphs and their exact modular periods using JS BigInt. The mixed-parent t=1 tree has 15 nodes/14 edges, 455 rows/343 distinct moduli, 15 valuation periods, and tree LCM 32,526,940,446,000. The h1a3 tree has 7 nodes/6 edges, 163 rows/160 distinct moduli, four valuation moduli, tree LCM 80,313,433,200, and final period 80,313,433,200. The h3a6 tree has 3 nodes/2 edges, 107 rows/105 distinct moduli, three valuation moduli, tree LCM 30,030,240,240, and final period 150,151,201,200. The 44-class h7a2/h7a4 subfamily was independently checked separately; its 180 rows have 109 distinct moduli (the duplicated modulus 649539 is shared by h7a2 node a=4 and h7a4 node a=2).

The audit reproduced all 14 mixed-parent t=1 edges and six leaves; all six h1a3 edges and both h3a6 edges; all 26 and 22 base-residue graphs; every listed cutoff; every low-a exceptional bound at the minimum base; the exact tree/prior LCMs; all period and valuation freezes; disjointness from the 28 old E-cones; pairwise distinctness of all 75 base residues modulo 1260; and the exact combined density 2615983/2039244004321524000. It also verified 3∤t throughout all five families, so the root valuation is exactly 7. This is an independent arithmetic reproduction, not a Python execution or Lean proof.

## Status and next action

This is a significant exact-arithmetic exclusion family, but it does not solve the seventh stratum, the Sheep machine, or BB(6). The local Python/shell tools have returned platform `ClientError`; none of the three Python checkers has been run here. Do not claim Lean verification or promote this to `results/`.

The highest-value next action is to formalize the five finite inverse graphs using `blank_even_inverse_cases`, the existing signed-gap theorem, and the residue-period lemmas, then compile with Lean 4.36.0-rc2 and run `#print axioms`. Agent 8, Agent 14, and Agent 40 have been asked to review the wrapper, source hypotheses, and high-(a) gaps. Preserve their substantive feedback and any counterexamples.
