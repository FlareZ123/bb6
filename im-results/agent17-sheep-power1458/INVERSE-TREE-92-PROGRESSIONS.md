# Seventh Sheep stratum: 93 inverse-tree progressions

**Agent 17's 20 November candidate, independently audited and extended by Agent 40 on 21 November 2026. The complete five-family theorem is now Lean-accepted in run [45293408209](https://github.com/FlareZ123/bb6/actions/runs/45293408209), using Lean 4.36.0-rc2.**

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

The density contributed by these 93 inverse-tree families among all exponent indices is
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

## Combined with the existing root-free direct census

The pre-existing direct-parent census in [`certificate.py`](certificate.py) and [`SheepPower1458RootGate.lean`](SheepPower1458RootGate.lean) covers another 132 residues
[
R_{\\rm free}=\\{t\\in[0,1260): 3\\nmid t,\\ t\\equiv0\\pmod4,\\ t\\not\\equiv5\\pmod7,\\ t\\not\\equiv1\\pmod9,\\ t\\not\\equiv8\\pmod{15}\\}.
]
For these residues the root has no generic predecessor; the existing exceptional-source bound excludes special predecessors. Their exponent-index density is (132/(1458\\cdot1260)=11/153090). An independent enumeration of the 70 root congruence rows reproduces exactly this same 132-element set.

These 132 classes are disjoint from the 93 inverse-tree classes: every one of the latter has at least one genuine generic root parent, and each of its periods freezes all root congruences. The 93 classes are also disjoint from the earlier 28 E-cones, as checked by their respective certificates. Thus the current seventh-stratum exclusion dossier contains **225 pairwise-disjoint infinite progressions** (132 direct-root-free plus 93 finite inverse-tree progressions), with combined density
[
\\delta_{225}=\\frac{11}{153090}+\\frac{2615983}{2039244004321524000}
=\\frac{146526124815583}{2039244004321524000}.
]
This remains a sparse partial exclusion, not a decision of the Sheep machine or BB(6).



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
with \(B\) of either sign. In the mixed \(t=1\pmod {T_0}\) tree, IDs 2, 3, and 4 have positive offsets \(B=22,358,3862\), respectively; all other nodes in that tree have \(B\le0\). Every node in the other four families has \(B\le0\). Every non-root node in those four families has \(v_3(Y(t)-1)=0\), so only hidden length \(h=0\) is possible there.

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

For every original even edge, Agent 14's SheepEvenSourceAlgebra.even_edge_to_algebra gives the generic and exceptional source equations. The root and every nonpositive-offset node are covered by blank_even_inverse_cases: for \(Y=(2^{1458t+s}+B)/C\) with \(B\le0\), take \(d=C\) and \(c=-B\), so \(dY+c=2^{1458t+s}\).

The mixed-parent \(t=1\) family has **three** positive-offset nodes: ID 2 \((s,B,C)=(5,22,135)\), ID 3 \((7,358,1215)\), and ID 4 \((9,3862,10935)\). ID 4 is a leaf, but its incoming edges must still be excluded. The compiled `SheepPower1458SourceIntegration.lean` provides the uniform `affine_edge_inverse_cases` splitter for both offset signs and the positive-offset `blank_even_inverse_cases_pos` wrapper, parameterized by arbitrary `b`; this covers all three nodes, including ID 4. Both source splitters were compiled in run [45293408209](https://github.com/FlareZ123/bb6/actions/runs/45293408209).

### Generic source branch: reuse the existing high- and low-a lemmas

For either offset sign, write the target as \(dY=2^n+b\), using \(b=0\) for \(B\le0\) and \(b=B\) for \(B>0\). The generic source splitter gives
\[
(d3^h)(2^{a+1}+1)v+2a(d3^h)+2^{h+1}d
=2^{n+h+1}+2^{h+1}b+3(d3^h).
\]
Put
\[
D=d3^h,\qquad E=2^{h+1}(d-b),\qquad n'=1458t+s+h+1.
\]
Moving the offset term to the left gives
\[
D(2^{a+1}+1)v+2aD+E=2^{n'}+3D.
\]

For \(a\ge A\), this is exactly the input equation of Agent 40's existing SheepGenericHigh.no_large_generic_equation. Its large_odd_gap lemma propagates the four cutoff conditions
\[
1<Q(D,E,A),\quad Q(D,E,A)\bmod2=1,\quad
Q(D,E,A)<2^A,\quad 2D\le2^A,
\]
where \(Q(D,E,a)=D(2a-3)+E\). Since \(d\) is odd and \(b\le d\), \(D\) is odd and \(E\) is even, so the parity condition is automatic. Only the numeric cutoff checks vary by node and hidden length.

For \(a<A\), rearrange the same equation as
\[
m v+Q(a)=2^{1458t+s+h+1},\qquad
m=D(2^{a+1}+1),\quad Q(a)=D(2a-3)+E.
\]
The existing \`SheepPower1458Core.no_generic\` is **not** directly sufficient: its finite hypothesis excludes hits at every residue in \`Fin cycle\`, whereas the tree certificate freezes only the listed base residue classes along \(t=r+Tk\). The exact bridge is a fixed-progression lemma: if \(P=1458T\), \(b=1458r+s+h+1\), \(2^P\equiv1\pmod m\), and \((2^b+\mathrm{shift})\not\equiv C\pmod m\), then no equation \(mv+C=2^{b+Pk}+\mathrm{shift}\) is possible. Encode \(Q(a)\) as \(C-\mathrm{shift}\), taking \(C=Q(a),\mathrm{shift}=0\) when \(Q(a)\ge0\), and \(C=0,\mathrm{shift}=-Q(a)\) otherwise. The period and base-residue facts are exactly what the existing certificates compute. `SheepPower1458.no_generic_fixed_period` implements the exact fixed-progression bridge and compiled successfully. The low-row table consumes it through `lowRow_no_generic_progression` and `lowRow_no_generic`; both also compiled in the accepted full-tree run. The cycle-wide `no_generic` theorem is not used as a substitute for progression-specific residue evidence.

### Exceptional source branch: one uniform divisibility gap

For a node \(Y=(2^{1458t+s}+B)/C\), either offset sign gives the same exceptional equation
\[
3D\,2^a+D(a+2)+S=2^N,\qquad
D=C3^h,\quad S=2^h(C-B),\quad N=1458t+s+h.
\]
Across all 29 node occurrences and all allowed hidden lengths, the exact certificate bounds are
\[
1\le D\le885735,\qquad 0<S\le3321979,\qquad N\ge1458.
\]
Use the common bound \(M=4{,}000{,}000\).

If \(a\le31\), then
\[
3D2^a+D(a+2)+S
\le 12{,}000{,}000\cdot2^{31}
   +4{,}000{,}000\cdot33+4{,}000{,}000
<2^{55}\le2^N.
\]
If \(a\ge32\), put \(L=D(a+2)+S\). At \(a=32\),
\[
0<L\le4{,}000{,}000\cdot34+4{,}000{,}000
=140{,}000{,}000<2^{32}.
\]
Since \(D\le4{,}000{,}000<2^{32}\le2^a\), the recurrence \(L(a+1)=L(a)+D\) proves \(0<L<2^a\) for every \(a\ge32\).

Now split on \(a\le N\). If \(a>N\), then \(3D2^a>2^N\), so equality is impossible. If \(a\le N\), then \(2^a\) divides \(2^N\) and \(3D2^a\); the equation would force \(2^a\mid L\), contradicting \(0<L<2^a\).

This proves the exceptional branch impossible for every node and every \(a\), with no per-node exceptional cutoffs and no logarithm/threshold selection. The older special-cutoff table in the arithmetic checker remains a redundant diagnostic, not a proof dependency.
### Finite graph closure

For a fixed progression parameter \(t\), let \(P_t(x)\) mean that \(x\) is one of the finitely many affine nodes in that family's inverse graph. The source work must show that every original predecessor of a node in \(P_t\) is either impossible (generic high/low branch or exceptional branch) or is one of the listed graph edges. Thus \(P_t\) is closed under taking original parents. Induction on EvenReach then sends any hypothetical path from \(10\) to the root target backwards into \(P_t(10)\), impossible because every listed node is greater than \(10\).

This packages the finite inverse graph as one parent-closed invariant rather than repeating a separate last-edge recursion for each edge. The invariant is formalized in `SheepPower1458TreeProof.lean`; `noEvenReachFiveFamilies` proves the conjunction for all five tables. The complete dependency closure compiled in run [45293408209](https://github.com/FlareZ123/bb6/actions/runs/45293408209), with transitive axiom profile `[propext, Classical.choice, Quot.sound]` and no `sorryAx`. The theorem excludes the specified progression targets in the exact `SheepEven.EvenReach` relation; it is not a decision of the Sheep machine or BB(6).

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

The audit reproduced all 14 mixed-parent t=1 edges and six leaves; all six h1a3 edges and both h3a6 edges; all 26 and 22 base-residue graphs; every listed cutoff; every low-a exceptional bound at the minimum base; the exact tree/prior LCMs; all period and valuation freezes; disjointness from the 28 old E-cones; pairwise distinctness of all 75 base residues modulo 1260; and the exact combined density 2615983/2039244004321524000. It also verified 3∤t throughout all five families, so the root valuation is exactly 7. This is an independent arithmetic reproduction, separate from the now-compiled Lean proof recorded below.

## Disjointness from Agent 14's 222-class sieve

The 93 progressions above occupy a new 3-adic valuation stratum, rather than duplicating Agent 14's earlier 222 classes in `im-results/agent14-sheep-inverse-dag-222/`.

For every one of the five stored residue lists in this dossier, each listed residue is nonzero modulo 3 and its corresponding period is divisible by 3. Hence every exponent in these progressions has
`v3(j)=v3(1458)+v3(t)=6`.

Agent 14's 222 classes are represented modulo `P=122472` by
`J=648+216*s+P*k=216(s+3+567*k)`,
where `0<=s<567` ranges over the 222 class indices. Reconstructing those indices from the maintained Agent 14 READMEs (the 133 lifted root-free classes, 41 additional root-free classes, and 48 nonempty-DAG roots) gives this distribution modulo 27:

| `s mod 27` | count |
|---:|---:|
| 0 | 7 |
| 2 | 21 |
| 5 | 21 |
| 6 | 21 |
| 9 | 21 |
| 11 | 21 |
| 14 | 21 |
| 15 | 12 |
| 17 | 14 |
| 18 | 21 |
| 20 | 21 |
| 23 | 21 |

In particular, no Agent 14 index is `24 mod 27). Since `3^4 | 567`, the valuation of `s+3+567*k` therefore equals that of `s+3`, which is at most 2. Thus every exponent in Agent 14's 222 classes has `v3(J)<=5`, for every `k>=0`.

Consequently, Agent 14's 222 classes (all `v3(J)<=5`) and the present 93 progressions (all `v3(j)=6`) are exactly disjoint. This is an arithmetic set comparison only; it does not strengthen the nonhalting conclusion or close the Lean acceptance gate.

## Status and next action

The complete five-family theorem is now Lean-accepted. Run [45293408209](https://github.com/FlareZ123/bb6/actions/runs/45293408209) compiled the exact dependency closure with Lean 4.36.0-rc2 at commit `f79ea4c7a6799611626b9d5904e969f227b452cd`. The exported `SheepPower1458.noEvenReachFiveFamilies` has axiom profile `[propext, Classical.choice, Quot.sound]`; no `sorryAx` appears. The source wrapper, progression-specific low-a bridge, high-a exclusion, exceptional-source bound, frozen root-edge tables, and parent-closure proof all compiled.

The local shell and Python tools returned platform `ClientError` before executing the bootstrap, so no local compiler run or Python checker run occurred in this invocation. Under the documented local-runtime fallback, the existing manual workflow was used once on a branch pinned to the exact source commit; no new workflow was created. This is a successful full-tree CI compilation, not a local preflight claim.

The theorem's scope is deliberately limited: it proves non-reachability for the five stated infinite progression families (75 base residues in their five periods, or 93 classes in the common-period presentation). The separate machine-source theorem `BB6.Agent16.SheepEvenSource.raw_halts_iff_even_power` was accepted earlier in [CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547); the present workflow compiles the `EvenReach` dependency chain but does not recompile `EvenSourceBridge.lean`. Together, these results rule out halting witnesses whose exponent belongs to the five excluded families, but leave all other possible halting exponents open. This does not decide the Sheep machine, the seventh stratum, or BB(6), and remains in `im-results/`.

Freeze the five-family list and do not spend further effort repeating period or row audits. The next mathematically meaningful direction is a broader invariant or a complete decision of the residual even-return orbit, rather than adding another disconnected residue family.
