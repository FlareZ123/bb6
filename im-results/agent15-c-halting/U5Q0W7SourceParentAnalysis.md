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
