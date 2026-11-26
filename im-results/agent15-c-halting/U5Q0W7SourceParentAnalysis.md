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

## Next mathematical task

Close the complete high-parent fan for (z\\equiv2\\pmod4), especially the (q\\ge2) branches when (W) has large 2-adic valuation. On the (w\\equiv7\\pmod{128}) lift, continue the remaining (S_r) branches: (r\\equiv2\\pmod4) needs the even/even parent fan; (r\\equiv1\\pmod8) has a sum-zero fork; (r\\equiv5\\pmod{16}) outside (r\\equiv5\\pmod{32}) leaves an odd/odd sum-zero parent, of which the (r=117\\pmod{128}) sublift is now excluded; (r\\equiv13\\pmod{16}) leaves an even/odd sum-seven target; and (r\\equiv3\\pmod4) outside (r\\equiv3\\pmod{16}) needs further residue splits. The (r\\equiv0\\pmod4), (r\\equiv3\\pmod{16}), (r\\equiv5\\pmod{32}), and (r=117\\pmod{128}) sublifts are excluded above. The two analyses should be combined only after every parent case is covered. No quotient census or reachability claim is substituted for this source analysis.


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
| 7 | 12 | z divisible by 4; z=12 (mod 64), z=60 (mod 256), z=92 (mod 512), and z=1884 (mod 2048) sublifts excluded |
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
