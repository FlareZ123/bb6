# Agent 7 review: omitted lower-valuation parents in the K3 third lift

**Review timestamp:** 2026-11-22T04:20:16.811Z  
**Scope:** `T0-K3-ODD-A-SECOND-LIFT.md`, `T0-K3-ODD-A-THIRD-LIFT.md`, and the exact `CascadeResetInverse.ResetParent` grammar in `FirstInverseComplete.lean`.

## Main issue

The odd arm of `ResetParent` is
`2*u+5 = 3^(t+1)*d`, with `d%2=1` and `2^t*d` in an odd source band. There is **no requirement that (3\nmid d)**. Thus (v_3(2u+5)=r) permits every (t=0,\ldots,r-1), not only (t=r-1). The second- and third-lift notes repeatedly call the largest-(t) branch “forced” and infer that a gap for its source parameter eliminates all odd parents. It does not eliminate the smaller-(t) branches.

## X ≡ 0 phase: a repair is available

When (v_3(X)=2) (the two non-high second-lift residues), or (v_3(X)=3) (the two non-high third-lift residues), (t=0) is still possible. Put (d=X/3). Since (X/p=(80-32x+(2K+13)/p)/3), for (x\in\mathcal W),
[
3 < d/p = (80-32x+(2K+13)/p)/9 < 4.
]
So (d) lies in the genuine odd source band at scale (K-1), and its parent is
[
h=2d-4p-K-4.
]
The exact normalized identity is
[
h/p=(124-64x-(5K+10)/p)/9,
]
which puts (2p<h<3p), the even-parent gap between scales (K-2) and (K-1). Also (3\mid d), (p\equiv2\pmod3), and (K\equiv0\pmod3), so (h\equiv0\pmod3), whence (2h+5\not\equiv0\pmod3). Thus this (t=0) parent is parentless. The (t=1) (or (t=2)) source-gap calculations in the notes can still be used, but they must be combined with this (t=0) parent analysis; the statement “there is no odd parent of (E)” is false.

## X ≡ 3 phase: the high Y lifts have an omitted t=0 branch

In the high (K\bmod162) class, (9\mid Y=2h+5). For either of the two (K\bmod486) lifts with (v_3(Y)=2), (t=0) is possible with (g=Y/3), not just (t=1) with source parameter (2g). The (t=0) source parameter satisfies
[
g/p=(248-128x+(25-10K)/p)/27,
]
which lies strictly between (3/2) and (2) on (mathcal W). Hence it is in the odd source band at scale (K-2), and
[
G=2g-2p-K-3
]
is a genuine parent of (h). The existing formula for (G/p) puts (p<G<3p/2), so (G) has no even parent; however (g\equiv0\pmod3) gives (G\equiv2\pmod3), so (3\mid 2G+5). The t=1 gap for (2g) does not eliminate this t=0 parent.

### Concrete exact instance

Take (a=15), (K=25815). Then (K\equiv3\pmod6), (K\equiv57\pmod{162}), (K\equiv57\pmod{486}), and
[
x=(2K+7)/2^{15}=51637/32768\in\mathcal W.
]
This is the high (K_1\equiv48-3a\pmod{54}) class, with (v_3(Y)=2). The exact parent enumerator from the full ResetParent grammar gives the following chain (ratios are shown only for readability):
[
E/p\approx4.928873
\xrightarrow[t=0,\ k=K-1]{\rm odd}
h/p\approx2.571831
\xrightarrow[t=0,\ k=K-2]{\rm odd}
G/p\approx1.429108
\xrightarrow[t=0,\ k=K-3]{\rm odd}
H/p\approx0.905478
\xrightarrow[k=K-3]{\rm even}
I/p\approx0.810956
\xrightarrow[k=K-3]{\rm even}
J/p\approx0.621913.
]
Here (J\not\equiv2\pmod3), so it has no odd parent, and (J) is in the even gap ((p/2,3p/4)), so it has no even parent. This does not refute the desired root-exclusion conclusion for this instance; it does refute the claim that the (t=1) gap alone leaves (h) parentless. The missing t=0 branch can continue through further parents and must be closed explicitly.

A quick independent residue audit over odd (a\bmod162) and the two non-high (Y\bmod27\in\{9,18\}) lifts gives (2G+5\bmod9\in\{0,3,6\}), 54 occurrences each. Thus the next (G)-parent split includes a genuine higher-valuation case; it is not uniformly a t=0 leaf. This is finite modular evidence, not a theorem.

## Additional proof-presentation points

1. In the first theorem’s canonical ray, the statement that all (J) edges are genuine even ResetParent edges should explicitly verify the target band for (0\le j<J): (u_0=16p-K-6\le16p-3), while
[
u_{J-1}=(16-2x)p+K+1\ge(16-13/4)p+K+1>12p-1
]
from (x\le13/8). Monotonicity then places every (u_j) in the scale-((K+1)) even band.

2. In the third-lift bound, the lower endpoint is attained: (4(80-32x)/81=901/648) at (x=415/256-1/1024). Replace the displayed strict lower inequality by (ge).

## Recommended next action

Do not count the two high-Y non-high lifts as excluded yet. Extend the exact inverse analysis from (G), retaining every (t<v_3(2G+5)), and either prove a uniform finite parentless chain (with a parameter-dependent depth bound) or record the residual higher-valuation families. The current 79/81 count is not source-proved until this omitted branch is closed. The X≡0 phase appears repairable by the explicit t=0 parentless argument above.
