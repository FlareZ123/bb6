# U5 q=0, w=7: exact source-parent reductions

Status: intermediate source analysis; **not** a blank-unreachability proof for the full w=7 progression.

## Root-facing parameter

The q=0 target from the odd/odd valuation-two inverse is
[
P_z=(3480+7224z,;3439+7140z),qquad t=81+168z.
]
The residual congruences give (z\equiv3\pmod5) (from (t\equiv0\pmod5)); the uniform 128-congruence gives, for (w=7+8s),
[
5z-7s\equiv12\pmod{16}.
]
Thus (z\equiv12\pmod{16}) is only the lift (w\equiv7\pmod{128}), not the whole w=7 progression.

Put (S=P_1+P_2=6919+14364z) and (T=S+1=6920+14364z=4(1730+3591z)). The original-source preimage grammar immediately yields:

- (z) odd: (v_2(T)=2), so only the (n=0) odd-a high branch is possible; its parent is
  [
  Q_z=(3457+7182z,;3447+7161z).
  ]
- (z\equiv0\pmod4): (v_2(T)=3), again only (n=0); the existing OddSevenSliver.lean theorem gives the same (Q_z). The sublift (z=12+64v) is now blank-unreachable by the two exact even-right inverses detailed below; the other z-divisible-by-four lifts remain open.
- (z\equiv2\pmod4): (v_2(T)\ge4), and there are additional even-depth high parents. This is the unresolved parent fan.

For (z\equiv2\pmod4), write (z=2+4u) and (W=2228+3591u), so (T=16W) and (P_1+2P_2=53366+86016u). Every high parent is indexed by an even depth (n=2q) with
[
U=a+3=2^{3-2q}W\quad(\text{an even natural}),qquad
k=\frac{53366+86016u-U-4-6q}{2}.
]
Equivalently (q=0,1) always occur, and (q\ge2) is permitted only when (2^{2q-2}\mid W). The (a=1) exceptional case is included by (U=4) if it occurs.

Two branches are already eliminated by source blank-image invariants:

- (q=0): ((a,k)=(8W-3,;17769+28644u)), whose right coordinate is odd and whose coordinate sum is (35590+57372u\equiv2\pmod4). Hence `blank_no_odd_sum_two` excludes it.
- (q=1): ((a,k)=(2W-3,;24450+39417u)). If (u\equiv1\pmod4), it is odd/odd with sum (28903+46599u\equiv2\pmod4), so `blank_no_odd_sum_two` excludes it. The subcylinder \(u=239+640r\) of the \(u\equiv3\pmod4\) case is now excluded by U5Q0W7U79Mod640.lean; the remaining \(u\equiv3\pmod4\) values and even \(u\) remain open.

Higher (q) occur only when (u\\equiv0\\pmod4), since (W\\equiv3u\\pmod4); larger (q) impose the exact stronger condition (2^{2q-2}\\mid W). They have not been closed.

## One exact w=7 lift

For (w\equiv7\pmod{128}), the residual congruence gives (z=12+16r). On this lift, the source chain is forced:
[
P_z\xleftarrow{\rm source}Q_z
\xleftarrow{\rm source}R_r
\xleftarrow{\rm source}S_r,
]
where
[
Q_z=(3457+7182z,;3447+7161z),
]
[
R_r=(89508+114744r,;89442+114660r),
]
[
S_r=(178948+229404r,;44720+57330r).
]
The first edge uses "odd_seven_parent_iff"; the second uses the odd/odd valuation-two inverse; the third uses the exact even-right predecessor theorem. The sum of (R_r) is
[
R_{r,1}+R_{r,2}=178950+229404r,
]
which is (6,2,6,2) modulo 8 as (r) ranges over residues (0,1,2,3) modulo 4. It is never 0 or 7, so the even-right inverse applies for every r.

The remaining target (S_r) has even right coordinate and sum
[
S_{r,1}+S_{r,2}=223668+286734r.
]
Its sum is 4,2,0,6 modulo 8 for (r=0,1,2,3) modulo 4. The (r=0) branch is now closed: the even-right inverse forces
[
T_r=(223666+286734r,;22359+28665r).
]
For (r=4v), this is
[
T_{4v}=(223666+1146936v,;22359+114660v),
]
whose right coordinate is odd and whose sum is (1) modulo 4. The source-certified "blank_no_odd_sum_one" excludes it. This is exactly the sublift (z=12+64v), formalized as a source-composition draft in "U5Q0W7Z4U3Mod16.lean". That file is not locally compiled, original-source CI checked, or axiom-audited.

The remaining S_r branches are now partitioned more finely. For (r=0\\pmod4), the next even-right inverse gives an odd-right sum-one target, closing the sublift (z=12+64v) in the uncompiled draft U5Q0W7Z4U3Mod16.lean. For (r=3\\pmod{16}), four successive even-right inverses after R_r lead to an odd-right sum-one target, closing (z=60+256t) in U5Q0W7Z4R3Mod16.lean. For (r=5\\pmod{32}), the chain reaches an even/odd target with sum 3 modulo 8; the exact section_evenodd_sum3_inverse forces an odd/odd predecessor with sum 2 modulo 4, excluded by blank_no_odd_sum_two. This closes (z=92+512q) in U5Q0W7R5Mod32.lean.

The remaining branches are open. For (r=2\\pmod4), S_r has sum 0 modulo 8 and the complete even/even parent fan is still required. For (r=1\\pmod8), the next inverse hits a sum-zero fork. For (r=5\\pmod8), the next target splits further: if (r=5\\pmod{16}), it is even/odd with sum 3 modulo 8, and its unique parent is odd/odd with sum (2+2s) modulo 4 for (r=5+16s); the (r=5\\pmod{32}) case is excluded. The (r=21\\pmod{32}) case has an odd/odd sum-zero parent; its (q=3\\pmod4) sublift is now excluded by the odd/odd low-value parent theorem, yielding (z=1884+2048s) in U5Q0W7R21Mod128.lean. The remaining q=0,1,2 modulo 4 cases still need parent analysis. If (r=13\\pmod{16}), the next target is even/odd with sum 7 modulo 8 and is not covered by the sum-three inverse. For (r=3\\pmod4) outside (r=3\\pmod{16}), further even-right inverses and residue splits remain. All four source-composition files are uncompiled and unaudited. This lift is only one of the sixteen lifts of (w\\equiv7\\pmod8).


## Exact parent fan for the remaining r=2 (mod 4) branch

Put (r=2+4v). The remaining even/even target after the first forced
even-right inverse is
[
X_v=(637756+917616v,\;159380+229320v),
\qquad X_{v,1}+X_{v,2}=8S_v,
]
where
[
S_v=99642+143367v=3(33214+47789v)>2.
]
The exact source theorem "even_even_parent_fan" therefore gives only
three possible parent shapes: direct/low, zero-left, or even-a bounce.
The zero-left alternative requires (S_v=2^n), which is impossible
because (S_v>2) is divisible by 3. Thus only direct and bounce parents
remain.

The direct parent is
[
D_v=(797134+1146936v,\;79689+114660v).
]
Its right coordinate is odd and its sum is
[
D_{v,1}+D_{v,2}=876823+1261596v\equiv7+4v\pmod8.
]
For odd v, the sum is 3 modulo 8, so "section_evenodd_sum3_inverse"
forces
[
F_v=(438409+630798v,\;259048+372729v).
]
This is odd/odd, with
[
F_{v,1}+F_{v,2}=697457+1003527v\equiv1+3v\pmod4.
]
Consequently the v=3 mod4 direct branch is excluded by
"blank_no_odd_sum_two"; the v=1 mod4 branch reaches an odd/odd
sum-zero target and requires the low-value parent analysis. For even v,
D_v has sum 7 modulo 8 and the sum-three inverse does not apply.

When (v\not\equiv2\pmod4), (S_v\not\equiv0\pmod4), and the specialized
"even_even_sumzero_parent" reduces the bounce alternative to the
depth-one parent
[
E_v=(199282+286734v,\;378612+544761v).
]
Its right coordinate is odd exactly when v is odd, and
[
E_{v,1}+E_{v,2}=577894+831495v\equiv2+3v\pmod4.
]
Thus v=1 mod4 is excluded by the odd-right sum-one invariant; v=3 mod4
leaves an odd-right sum-three state; and v=0 mod4 leaves an even-right
state, to which further even-right inverses apply.

For (v=2+4q), (S_v\equiv0\pmod4), so the two-parent specialization is
not valid. The complete "even_even_parent_fan" still excludes the
zero-left branch, but its even-a bounce may have any odd depth n
satisfying
[
n\le v_2(S_v)+1.
]
Here
[
S_v=12(32198+47789q),
]
and the odd coefficient 47789 makes this secondary valuation unbounded
over q. The n=1 bounce is E_v; higher odd depths remain a genuine
nested parent fan. This is the main unresolved fork in the r=2 mod4
lift. No reachability exclusion is claimed for D_v or the remaining
bounce alternatives.

## Next mathematical task

Continue the remaining q=1 parent residues in the (z\\equiv2\\pmod4) sector and the even-(W) high-depth cases. The exact source parent fan is now proved: every parent has even depth (n) and satisfies the scale/cost equations; when (W) is odd, only depths 0 and 2 remain. On the (w\\equiv7\\pmod{128}) lift, continue the remaining (S_r) branches: (r\\equiv2\\pmod4) needs the even/even parent fan; (r\\equiv1\\pmod8) has a sum-zero fork; (r\\equiv5\\pmod{16}) outside (r\\equiv5\\pmod{32}) leaves an odd/odd sum-zero parent, of which the (r=117\\pmod{128}) sublift is now excluded; (r\\equiv13\\pmod{16}) leaves an even/odd sum-seven target; and (r\\equiv3\\pmod4) outside (r\\equiv3\\pmod{16}) needs further residue splits. The (r\\equiv0\\pmod4), (r\\equiv3\\pmod{16}), (r\\equiv5\\pmod{32}), and (r=117\\pmod{128}) sublifts are excluded above. The u=79+80T branch now has T=2 (mod 8) excluded by U5Q0W7U79Mod640.lean; the other seven T (mod 8) classes remain open. The two analyses should be combined only after every parent case is covered. No quotient census or reachability claim is substituted for this source analysis.


## Infinite subfamily closed by the first parent fan

If (u\equiv1\pmod4), then (W=2228+3591u\equiv3\pmod4) is odd.
The parent equation
[
2^{n+1}(a+3)=16W
]
with (n) even and (a\ge1) forces (n\le2): if (n\ge4), its
left side is divisible by 32 while (16W\equiv16\pmod{32}).
Thus only (n=0,2) occur. Both parent families are excluded by the
existing `blank_no_odd_sum_two` theorem, as recorded above. Therefore
[
\neg CReach(P_{2+4u,1},P_{2+4u,2})
\quad\text{for every }u\equiv1\pmod4.
]
This is the full cylinder (z\equiv6\pmod{16}); intersecting with the
actual residual condition (z\equiv3\pmod5) gives
(z\equiv38\pmod{80}).

The Lean proof attempt is in
`U5Q0W7ParentFan.lean`; it passed the exact-source closure in workflow run #17.
The parent fan and the u=1 (mod 4) target exclusion have printed axioms
[propext, Classical.choice, Quot.sound], with no sorryAx/native_decide dependency.


The same excluded cylinder has a direct root-index description. Write
(w=7+8s). Combining the exact residual congruence
(t\equiv16+23w\pmod{128}) with (t=81+168z) gives
(5z-7s\equiv12\pmod{16}). Hence
[
z\equiv6\pmod{16}
\quad\Longleftrightarrow\quad
s\equiv14\pmod{16}
\quad\Longleftrightarrow\quad
w\equiv119\pmod{128}.
]
Therefore the source-only exclusion above removes the actual root-index
cylinder (w\equiv119\pmod{128}) from the w=7 progression.


## Two further odd-z cylinders

For (z\equiv5\) or (13\pmod{16}), the first parent is uniquely
(Q_z): (P_z) is even/odd and
((P_{z,1}+P_{z,2}+1)\equiv4\pmod8), so
`evenodd_four_parent_iff` applies. Here (z\equiv5\pmod8), so
(Q_z) is odd/even with coordinate sum (3\pmod8); the exact
`section_odd_even_iff_affine` theorem forces its unique parent
[
R_z=(6902+14343z,;(3445+7161z)/2).
]
This is odd/odd, its right coordinate is odd, and
[
R_{z,1}+R_{z,2}=(17249+35847z)/2\equiv2\pmod4.
]
The existing `blank_no_odd_sum_two` invariant therefore excludes
(R_z), and hence (P_z), for both residue classes.

The residual map (5z-7s\equiv12\pmod{16}), (w=7+8s), translates
these two exclusions into
[
z\equiv5\pmod{16}\Rightarrow w\equiv95\pmod{128},\qquad
z\equiv13\pmod{16}\Rightarrow w\equiv31\pmod{128}.
]
The corresponding Lean draft is
`w7_q0_target_unreachable_z5or13mod16` in
`U5Q0W7ParentFan.lean`; it passed the exact-source closure in workflow run #17.


## One higher-depth root cylinder: w=439 (mod 512)

The remaining q=1 branch in (z\\equiv2\\pmod4) has a further exact
source closure on (w\\equiv439\\pmod{512}). The exact residual modulo
512 on w=7+8s is t \\equiv 272+23w \\equiv 433+184s \\pmod{512}.
With t=81+168z, division by 8 gives
21z \\equiv 44+23s \\pmod{64}, hence
z \\equiv 60+59s \\pmod{64}. For w=439, s=54, so
z \\equiv46\\pmod{64}; intersecting with the exact
z \\equiv3\\pmod5 residual yields z \\equiv238\\pmod{320}, hence
u=(z-2)/4 \\equiv59\\pmod{80}.

Write (u=59+80v). Then (W=2228+3591u) is odd, so the first-parent
fan has only q=0 and q=1. The q=0 parent is already excluded. The q=1
parent is
[
A_1=(428191+574560v,;2350053+3153360v).
]
Its coordinates are odd/odd and its sum is
(2778244+3727920v\equiv4\pmod{16}). The unique odd/odd low-value
parent is therefore
[
B=(1389120+1863960v,;1869585+2508660v).
]
The right coordinate of (B) is odd and
[
B_1+B_2=3258705+4372620v\equiv1\pmod4.
]
Thus `blank_no_odd_sum_one` excludes (B), hence (A_1), hence the
q=1 branch. Together with q=0 exclusion and the absence of higher
depths, this excludes (P_z) on (w\equiv439\pmod{512}).

This exact source derivation is now represented in
`U5Q0W7ParentFan.lean` by `w7_z2_q1_parent_unreachable_u59mod80` and
`w7_q0_target_unreachable_u59mod80`. The first applies the exact
odd/odd sum-four parent theorem and the existing odd-right sum-one
blank-image invariant; the second uses the complete q-parent fan and
oddness of W to eliminate every depth except 0 and 2. Both declarations were compiled and explicitly axiom-printed in workflow
runs #17 and #20. Their dependencies are [propext, Classical.choice, Quot.sound],
with no sorryAx/native_decide dependency. This closes the target-level q=0
branch on the (w\\equiv439\\pmod{512}) lift only; it does not close the
other lifts of the (u\\equiv3\\pmod4) branch.


## Complete 128-lift lookup for the w=7 progression

For quick navigation, the residual map (z\equiv12+11s\pmod{16}),
(w=7+8s), gives:

| w (mod 128) | z (mod 16) | first-parent sector |
|---:|---:|---|
| 7 | 12 | z divisible by 4; z=12 (mod 64), z=60 (mod 256), z=92 (mod 512), and z=1884 (mod 2048) sublifts excluded |
| 15 | 7 | z odd |
| 23 | 2 | z=2 mod 4 |
| 31 | 13 | z odd; excluded |
| 39 | 8 | z divisible by 4 |
| 47 | 3 | z odd |
| 55 | 14 | z=2 mod 4; q=1 parent excluded on u=7 mod 32, u=35 mod 64, u=59 mod 80, u=23 mod 512, u=339 mod 2560, u=499 mod 1280, and u=3379 mod 5120 |
| 63 | 9 | z odd |
| 71 | 4 | z divisible by 4 |
| 79 | 15 | z odd |
| 87 | 10 | z=2 mod 4 |
| 95 | 5 | z odd; excluded |
| 103 | 0 | z divisible by 4 |
| 111 | 11 | z odd |
| 119 | 6 | z=2 mod 4; excluded |
| 127 | 1 | z odd |

The additional (w\equiv439\pmod{512}) closure is a deeper lift of
the (w\equiv55\pmod{128}) row. This table is a routing aid, not a
claim that the remaining rows are reachable or unreachable.




## Additional q=1 parent exclusions on the w=55 (mod 128) row

The parent fan reduces the q=0 target to
\[
Q(u)=(2W-3,\;24450+39417u),\qquad W=2228+3591u,
\]
whenever \(W\) is odd. Four disjoint infinite parameter slices of \(Q(u)\)
are now excluded. The \(u=59+80t\) branch is the previously established
odd/odd sum-four parent followed by the odd-right sum-one obstruction;
see the detailed derivation above.

### u=7+32t

The q=1 parent is
\[
A=(54727+229824t,\;300369+1261344t).
\]
The odd/odd low-valuation inverse forces
\[
B=(177546+745584t,\;238956+1003464t),
\]
which is even/even with \(B_x+B_y\equiv2\pmod8\). The exact even/even
unique-parent theorem forces
\[
C=(416500+1749048t,\;119477+501732t).
\]
Here \(C_y\) is odd and \(C_x+C_y\equiv1\pmod4\), so the original-source
odd-right sum-one invariant excludes \(C\). This is formalized by
w7_z2_q1_parent_unreachable_u7mod32 and
w7_q0_target_unreachable_u7mod32 in U5Q0W7U7Mod32.lean.

### u=35+64t

The q=1 parent is
\[
A=(255823+459648t,\;1404045+2522688t).
\]
The odd/odd low-valuation inverse forces
\[
B=(829932+1491168t,\;1116987+2006928t),
\]
with \((B_x+B_y+1)\equiv8\pmod{16}\). The exact odd-seven parent
forces
\[
C=(973457+1749048t,\;1045221+1877988t).
\]
Here \(C_y\) is odd and \(C_x+C_y\equiv2\pmod4\), so the original-source
odd-right sum-two invariant excludes \(C\). This is formalized by
w7_z2_q1_parent_unreachable_u35mod64 and
w7_q0_target_unreachable_u35mod64 in U5Q0W7U3Mod64.lean.

### u=23+512s

The q=1 parent is
\[
A=(169639+3677184s,\;931041+20181504s).
\]
The odd/odd low-valuation inverse forces
\[
B=(550338+11929344s,\;740688+16055424s),
\]
which is even/even with \(B_x+B_y\equiv2\pmod8\). The even/even unique
parent forces
\[
C=(1291024+27984768s,\;370343+8027712s).
\]
Here \(C_x\) is even, \(C_y\) is odd, and
\(C_x+C_y+1\equiv8\pmod{16}\). The odd-seven parent forces
\[
D=(830681+18006240s,\;600511+13016976s).
\]
This is odd/odd with \(D_x+D_y\equiv8\pmod{16}\), so its odd/odd
low-valuation parent is
\[
E=(715594+15511608s,\;658051+14264292s).
\]
The right coordinate of \(E\) is odd and \(E_x+E_y\equiv1\pmod4\);
the original-source odd-right sum-one invariant excludes it. This is
formalized by w7_z2_q1_parent_unreachable_u23mod512 and
w7_q0_target_unreachable_u23mod512 in U5Q0W7U23Mod512.lean.

### u=339+2560v

The q=1 parent and forced predecessors are
\[
\begin{aligned}
A&=(2439151+18385920v,\;13386813+100907520v),\\
B&=(7912980+59646720v,\;10649895+80277120v),\\
C&=(9281435+69961920v,\;9965664+75119520v),\\
D&=(19247097+145081440v,\;4982831+37559760v),\\
F&=(12114962+91320600v,\;8548895+64440180v).
\end{aligned}
\]
The exact source steps are odd/odd low-value, even/odd sum-three,
even-right six, and odd/odd low-value. The terminal state has odd right
coordinate and
\[
F_x+F_y=20663857+155760780v\equiv1\pmod4.
\]
The original-source odd-right sum-one invariant excludes F, hence A.
This is formalized by w7_z2_q1_parent_unreachable_u339mod2560 and
w7_q0_target_unreachable_u339mod2560 in U5Q0W7U19Mod2560.lean.

### u=499+1280v

The forced chain is
\[
\begin{aligned}
A&=(3588271+9192960v,\;19693533+50453760v),\\
B&=(11640900+29823360v,\;15667215+40138560v),\\
C&=(13654055+34980960v,\;14660634+37559760v),\\
D&=(28314687+72540720v,\;7330316+18779880v),\\
E&=(35645001+91320600v,\;3665157+9389940v).
\end{aligned}
\]
The source steps are odd/odd low-value, even/odd sum-three, then two
even-right six inverses. The terminal state has odd right coordinate and
\[
E_x+E_y=39310158+100710540v\equiv2\pmod4.
\]
The original-source odd-right sum-two invariant excludes E, hence A.
This is formalized by w7_z2_q1_parent_unreachable_u499mod1280 and
w7_q0_target_unreachable_u499mod1280 in U5Q0W7U19Mod2560.lean.

### u=3379+5120v

The forced chain is
\[
\begin{aligned}
A&=(24272431+36771840v,\;133214493+201815040v),\\
B&=(78743460+119293440v,\;105978975+160554240v),\\
C&=(92361215+139923840v,\;99170094+150239040v),\\
D_1&=(191531307+290162880v,\;49585046+75119520v),\\
D_2&=(241116351+365282400v,\;24792522+37559760v),\\
D_3&=(265908871+402842160v,\;12396260+18779880v),\\
F&=(278305129+421622040v,\;6198129+9389940v).
\end{aligned}
\]
After the odd/odd low-value and even/odd sum-three steps, four exact
even-right six inverses reach F. Its right coordinate is odd and
\[
F_x+F_y=284503258+431011980v\equiv2\pmod4.
\]
The original-source odd-right sum-two invariant excludes F, hence A.
This is formalized by w7_z2_q1_parent_unreachable_u3379mod5120 and
w7_q0_target_unreachable_u3379mod5120 in U5Q0W7U19Mod2560.lean.

### u=2739+10240v

The q=1 parent and forced source predecessors are
\[
\begin{aligned}
A&=(19675951+73543680v,\;107987613+403630080v),\\
B&=(63831780+238586880v,\;85909695+321108480v),\\
C&=(74870735+279847680v,\;80390214+300478080v),\\
D_1&=(155260947+580325760v,\;40195106+150239040v),\\
D_2&=(195456051+730564800v,\;20097552+75119520v),\\
D_3&=(215553601+805684320v,\;10048775+37559760v),\\
F&=(112801186+421622040v,\;61424979+229590900v).
\end{aligned}
\]
The source steps are odd/odd low-value, even/odd sum-three, three
even-right six inverses, and odd/odd low-value. The terminal state has
odd right coordinate and
\[
F_x+F_y=174226165+651212940v\equiv1\pmod4.
\]
The original-source odd-right sum-one invariant excludes F, hence A.
This is formalized by w7_z2_q1_parent_unreachable_u2739mod10240 and
w7_q0_target_unreachable_u2739mod10240 in U5Q0W7U19Mod2560.lean.

### u=9939+10240v

The forced chain is
\[
\begin{aligned}
A&=(71386351+73543680v,\;391790013+403630080v),\\
B&=(231588180+238586880v,\;311689095+321108480v),\\
C&=(271638635+279847680v,\;291663864+300478080v),\\
D_1&=(563302497+580325760v,\;145831931+150239040v),\\
D_2&=(354567212+365282400v,\;250199570+257760720v),\\
D_3&=(604766780+623043120v,\;125099784+128880360v),\\
F&=(729866562+751923480v,\;62549891+64440180v).
\end{aligned}
\]
The source steps are odd/odd low-value, even/odd sum-three,
even-right six, odd/odd low-value, then two even-right six inverses.
The terminal state has odd right coordinate and
\[
F_x+F_y=792416453+816363660v\equiv1\pmod4.
\]
The original-source odd-right sum-one invariant excludes F, hence A.
This is formalized by w7_z2_q1_parent_unreachable_u9939mod10240 and
w7_q0_target_unreachable_u9939mod10240 in U5Q0W7U19Mod2560.lean.

### u=16339+20480v

The forced chain is
\[
\begin{aligned}
A&=(117351151+147087360v,\;644058813+807260160v),\\
B&=(380704980+477173760v,\;512381895+642216960v),\\
C&=(446543435+559695360v,\;479462664+600956160v),\\
D_1&=(926006097+1160651520v,\;239731331+300478080v),\\
D_2&=(582868712+730564800v,\;411300020+515521440v),\\
D_3&=(994168730+1246086240v,\;205650009+257760720v),\\
F&=(599909367+751923480v,\;402779687+504842100v).
\end{aligned}
\]
The exact source steps are odd/odd low-value, even/odd sum-three,
even-right six, odd/odd low-value, even-right six, and even/odd
sum-three. The terminal state has odd right coordinate and
\[
F_x+F_y=1002689054+1256765580v\equiv2\pmod4.
\]
The original-source odd-right sum-two invariant excludes F, hence A.
The q=0 lift uses the generic odd-W parent-fan lemma
w7_q0_target_unreachable_of_q1.

### u=20019+20480v

After odd/odd low-value and even/odd sum-three, six exact even-right
inverses reach
\[
\begin{aligned}
D_1&=(1134560667+1160651520v,\;293723486+300478080v),\\
D_2&=(1428284151+1461129600v,\;146861742+150239040v),\\
D_3&=(1575145891+1611368640v,\;73430870+75119520v),\\
D_4&=(1648576759+1686488160v,\;36715434+37559760v),\\
D_5&=(1685292191+1724047920v,\;18357716+18779880v),\\
F&=(1703649905+1742827800v,\;9178857+9389940v).
\end{aligned}
\]
The initial q=1 parent is
\[
A=(143780911+147087360v,\;789113373+807260160v).
\]
The terminal state has odd right coordinate and
\[
F_x+F_y=1713828762+1752217740v\equiv2\pmod4.
\]
The original-source odd-right sum-two invariant excludes F, hence A.
The q=0 lift again uses w7_q0_target_unreachable_of_q1.

### u=1939+2560v: exact sum-seven parent obstruction

The q=1 parent and its first two predecessors are
\[
\begin{aligned}
A&=(13930351+18385920v,\;76454013+100907520v),\\
B&=(45192180+59646720v,\;60823095+80277120v),\\
C&=(53007635+69961920v,\;56915364+75119520v).
\end{aligned}
\]
A is odd/odd and uses the original low-value inverse; B is even/odd
with coordinate sum 3 mod 8 and uses the exact even/odd sum-three
inverse. At C, the exact residues are
\[
\begin{aligned}
C_x+C_y&\equiv7\pmod8,\\
C_x+C_y+1&\equiv8\pmod{16},\\
C_x+C_y+1&\equiv24\pmod{32},\\
C_x&\equiv3\pmod4,\qquad C_y\equiv4\pmod8.
\end{aligned}
\]
These are precisely the hypotheses of
BB6.Agent19HighEvenRight.sum7_every_parent_odd_image. Every exact
parent of C lies in the forbidden odd-right sum-two image, so C and
then A are blank-unreachable. This is a direct source-parent obstruction,
not merely a terminal result of the finite forced normalizer.

The original q=0 target is excluded using the generic odd-W parent-fan
lift w7_q0_target_unreachable_of_q1.

### Root residuals and exact-source verification

For all thirteen slices, \(z=2+4u\equiv14\pmod{16}\). The necessary
root relation \(5z-7r\equiv12\pmod{16}\), with \(w=7+8r\), gives
\(r\equiv6\pmod{16}\) and \(w\equiv55\pmod{128}\). The root condition
\(z\equiv3\pmod5\) requires \(t\equiv1\pmod5\) in the
\(u=7+32t\) and \(u=35+64t\) slices; it requires \(s\equiv3\pmod5\)
for \(u=23+512s\); and it holds for every \(t\) in the
\(u=59+80t\) slice. The eight new slices
\[
u=339+2560v,\;499+1280v,\;3379+5120v,\;2739+10240v,\;
9939+10240v,\;16339+20480v,\;20019+20480v,\;1939+2560v
\]
all have \(u\equiv19\pmod{20}\) for every parameter value, so no
further root restriction is needed. The \(u=59+80t\) slice is the
deeper \(w\equiv439\pmod{512}\) lift. These are necessary root filters,
not a classification of the full row.

### Quantified coverage of the root-compatible u family

Write every root-compatible parameter as \(u=19+20n\), and split
\(n\) into its four residue classes modulo 4.

- \(n=4T\), so \(u=19+80T\). The nine pairwise-disjoint proved
  cylinders are
  \[
  T\equiv1\pmod4,\quad T\equiv4\pmod{32},\quad
  T\equiv6\pmod{16},\quad T\equiv42\pmod{64},
  \]
  \[
  T\equiv34\pmod{128},\quad T\equiv124\pmod{128},\quad
  T\equiv204\pmod{256},\quad T\equiv250\pmod{256},\quad
  T\equiv24\pmod{32}.
  \]
  Their density within this branch is
  \[
  \frac14+\frac1{32}+\frac1{16}+\frac1{64}
  +\frac1{128}+\frac1{128}+\frac1{256}+\frac1{256}
  +\frac1{32}=\frac{53}{128}.
  \]

- \(n=4T+1\), so \(u=39+80T\). The proved cylinders are
  \(T\) even (the \(u=7+32t\) family) and
  \(T\equiv19\pmod{32}\) (the \(u=23+512s\) family).
  They are disjoint and have density
  \(\frac12+\frac1{32}=\frac{17}{32}\).

- \(n=4T+2\), so \(u=59+80T\). The entire branch is covered,
  with density \(1\).

- \(n=4T+3\), so \(u=79+80T\). The subcylinder \(T\equiv2\pmod8\),
  equivalently \(u=239+640r\), is source-accepted and has density \(1/8\)
  within this branch. The other seven \(T\pmod8\) classes remain open.

The four branches are disjoint and equally frequent. Therefore the
union of the thirteen source-proved exclusions has natural density
\[
\frac14\left(\frac{53}{128}+\frac{17}{32}+1+\frac18\right)
=\frac{265}{512}
\]
among all \(u\equiv19\pmod{20}\). This is an exact density for the
union of the proved cylinders, hence a lower bound on the density of
all excluded targets in this root-compatible family. It is not a
classification of the complement.

### Exact-source verification

The focused exact-source closure target w7-q0-parent-fan passed in run
#20 (GitHub Actions run 45796426913) for the original four roots. The
seven-slice closure passed in run #25 (45832100735), the nine-slice
closure in run #26 (45833176482), and the twelve-slice closure in run
#28 (45834843362). Run #28 compiles U5Q0W7U19Mod2560.lean, the generic
odd-W q=0 lift, the sum-seven source-parent helper, and all sixteen new
q=0/q=1 declarations. The module explicitly prints their axioms; the
workflow grep guard found no sorryAx or native_decide dependency.
The thirteenth u=239+640r subcylinder passed the original-source closure
in run #46 (45903781364). That run additionally compiles
MixedOdd16TwoOrbit, U5Q0W7ParentFan, U5Q0W7U19Mod2560,
M0EvenEvenSumZero, and U5Q0W7U79Mod640.lean. Both new theorem axiom
profiles are [propext, Classical.choice, Quot.sound]; the workflow
guard found no sorryAx or _native dependency.

These are thirteen infinite excluded sublifts of the q=1 parent, not a
classification of the entire w=55 (mod 128) row. The remaining q=1
parameter residues (including the other seven T mod 8 classes in u=79+80T) and all even-W high-depth cases remain open.


## 2026-11-26: source-accepted u=239+640r subcylinder

The previously open \(u=79+80T\) branch has its first exact-source
subcylinder closed: \(T=2+8r\), i.e. \(u=239+640r\). Its q=1 parent is
\[
Q=(1720951+4596480r,\;9445113+25226880r),
\]
an odd/odd target with right coordinate at least 64 and sum \(16\pmod{32}\).
The exact odd/odd sum-16 iff gives precisely
\[
P_0=(5583030+14911680r,\;7514070+20069280r),\qquad
P_2=(1395756+3727920r,\;9607704+25661160r).
\]
Both have even right coordinate and sum \(4\pmod8\). Three exact
six-even-right inverses from \(P_0\) reach
\[
(18732644+50032920r,\;939257+2508660r),
\]
and one from \(P_2\) reaches
\[
(11003458+29389080r,\;4803851+12830580r).
\]
Each terminal state has odd right coordinate and sum \(1\pmod4\), so
the original-source blank_no_odd_sum_one invariant excludes both parent
branches. The generic odd-W q=0 lift then excludes
\[
P(u)=(6924072+18493440r,\;6843559+18278400r).
\]
The proof is formalized in
[U5Q0W7U79Mod640.lean](U5Q0W7U79Mod640.lean), with a readable derivation in
[U5Q0W7U79Mod640.md](U5Q0W7U79Mod640.md). Original-source run #46
(45903781364) passed; both new theorems print axioms
[propext, Classical.choice, Quot.sound], with no sorryAx or native
evaluation dependency. For this cylinder, z=2+4u=958+2560r, so z=14 (mod 16) and z=3 (mod 5); it is compatible with the same w=55 (mod 128) root row as the other listed slices. The new cylinder has density \(1/8\) within
\(u=79+80T\), raising the root-compatible \(u\equiv19\pmod{20}\)
excluded density lower bound from \(249/512\) to \(265/512\). It does
not close the other seven \(T\pmod8\) classes or decide Machine C.
