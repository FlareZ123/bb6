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
- (z\equiv0\pmod4): (v_2(T)=3), again only (n=0); the existing `OddSevenSliver.lean` theorem gives the same (Q_z).
- (z\equiv2\pmod4): (v_2(T)\ge4), and there are additional even-depth high parents. This is the unresolved parent fan.

For (z\equiv2\pmod4), write (z=2+4u) and (W=2228+3591u), so (T=16W) and (P_1+2P_2=53366+86016u). Every high parent is indexed by an even depth (n=2q) with
[
U=a+3=2^{3-2q}W\quad(\text{an even natural}),qquad
k=\frac{53366+86016u-U-4-6q}{2}.
]
Equivalently (q=0,1) always occur, and (q\ge2) is permitted only when (2^{2q-2}\mid W). The (a=1) exceptional case is included by (U=4) if it occurs.

Two branches are already eliminated by source blank-image invariants:

- (q=0): ((a,k)=(8W-3,;17769+28644u)), whose right coordinate is odd and whose coordinate sum is (35590+57372u\equiv2\pmod4). Hence `blank_no_odd_sum_two` excludes it.
- (q=1): ((a,k)=(2W-3,;24450+39417u)). If (u\equiv1\pmod4), it is odd/odd with sum (28903+46599u\equiv2\pmod4), so `blank_no_odd_sum_two` excludes it. The cases (u\equiv3\pmod4) and (u) even remain.

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
The first edge uses `odd_seven_parent_iff`; the second uses the odd/odd valuation-two inverse; the third uses the complete even/even parent fan and the fact
(R_{r,1}+R_{r,2}=178950+229404r\equiv6) or (2\pmod8).

The remaining target (S_r) has
[
S_{r,1}+S_{r,2}=223668+286734r,
]
which is divisible by 8 exactly for (r\equiv2\pmod4). No conclusion is claimed for its remaining fan. This lift is only one of the sixteen lifts of (w\equiv7\pmod8).

## Next mathematical task

Close the complete high-parent fan for (z\equiv2\pmod4), especially the (q\ge2) branches when (W) has large 2-adic valuation; separately handle the (S_r) fan on the (w\equiv7\pmod{128}) lift. The two analyses should be combined only after every parent case is covered. No quotient census or reachability claim is substituted for this source analysis.


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
`U5Q0W7ParentFan.lean`; it awaits independent local compilation.
Until that preflight succeeds, this is a source-level derivation with a
pending formalization, not a verified Lean theorem.


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
`U5Q0W7ParentFan.lean`; it also awaits independent local compilation.


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
oddness of W to eliminate every depth except 0 and 2. Both declarations
remain uncompiled and unaudited. This closes the target-level q=0 branch
on the (w\\equiv439\\pmod{512}) lift only; it does not close the other
lifts of the (u\\equiv3\\pmod4) branch.


## Complete 128-lift lookup for the w=7 progression

For quick navigation, the residual map (z\equiv12+11s\pmod{16}),
(w=7+8s), gives:

| w (mod 128) | z (mod 16) | first-parent sector |
|---:|---:|---|
| 7 | 12 | z divisible by 4 |
| 15 | 7 | z odd |
| 23 | 2 | z=2 mod 4 |
| 31 | 13 | z odd; excluded |
| 39 | 8 | z divisible by 4 |
| 47 | 3 | z odd |
| 55 | 14 | z=2 mod 4 |
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

## 2026-11-26: z=12 (mod 64) sublift in the z divisible-by-four sector

Set \(u=3+16v\) and \(z=4u=12+64v\). The q=0 target and its forced parents are
\[
\begin{aligned}
P_z&=(90168+462336v,\;89119+456960v),\\
Q_z&=(89641+459648v,\;89379+458304v),\\
R_0&=(89508+458976v,\;89442+458640v).
\end{aligned}
\]
The exact "odd_seven_parent_iff" theorem forces \(P_z\to Q_z\), since
\((P_{z,1}+P_{z,2}+1)\equiv8\pmod{16}\). The exact "oddodd_parent_iff"
then forces \(Q_z\to R_0\), since \(Q_z\) is odd/odd and its sum is
\(4\bmod8\).

The right coordinate of \(R_0\) is even and its sum is
\[
R_{0,1}+R_{0,2}=178950+917616v\equiv6\pmod8.
\]
The source-certified "blank_reach_iff_even_right" therefore forces
\[
R_1=(178948+917616v,\;44720+229320v).
\]
Its right coordinate is again even and its sum is
\[
R_{1,1}+R_{1,2}=223668+1146936v\equiv4\pmod8.
\]
A second application forces
\[
R_2=(223666+1146936v,\;22359+114660v).
\]
Here the right coordinate is odd and
\[
R_{2,1}+R_{2,2}=246025+1261596v\equiv1\pmod4.
\]
The exact "blank_no_odd_sum_one" invariant excludes \(R_2\). Hence
\(P_z\) is blank-unreachable for every \(v\ge0\).

The source composition is drafted in
"U5Q0W7Z4U3Mod16.lean". It is a target-level sublift exclusion only:
it does not close all \(z\equiv0\pmod4\), and the composed Lean file
has not been locally compiled, original-source CI checked, or axiom-audited.
