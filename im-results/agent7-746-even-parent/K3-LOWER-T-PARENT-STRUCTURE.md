# K3 high-Y branch: exact lower-t parents omitted by the third-lift gap

**Status:** intermediate correction and branch analysis; not a BB(6) result and not Lean-certified. This note is based on the exact `CascadeResetInverse.ResetParent` grammar in `im-results/agent10-cascade/FirstInverseComplete.lean`. It supersedes no source theorem; it identifies an omitted parent family in the paper-level K3 lift argument.

## 1. Valuation does not force the maximal odd exponent

The exact odd arm is
[
2u+5=3^{t+1}d,quad dequiv1pmod2,quad
6cdot2^k+1le2^tdle8cdot2^k-1,
]
together with
[
2(2^td)=8cdot2^k+h+k+5.
]
There is no condition (3\nmid d). If (v_3(2u+5)=r), every (t=0,1,ldots,r-1) is an algebraic candidate; each must be tested against its own dyadic source band. A gap for the maximal-(t) candidate does not exclude the lower-(t) candidates.

This affects both the second-lift (X\equiv0\pmod9) argument and the third-lift high-(Y) argument.

## 2. The (X\equiv0\pmod9) cases can be repaired by the omitted (t=0) parent

Use (p=2^K), (x=(2K+7)/2^a\in\mathcal W), and
[
X=2E+5=\frac{80p+2K+13-2(2K+7)2^{K+4-a}}3.
]
For the non-high second-lift cases (v_3(X)=2), and for the non-high third-lift cases (v_3(X)=3), (t=0) is possible. Put (d=X/3). Then
[
rac dp=\frac{80-32x+(2K+13)/p}{9}.
]
On (mathcal W=[803/512,1659/1024]) (where the upper endpoint is (415/256-1/1024)), this lies strictly between (3) and (4). Hence (d) is in the odd source band at scale (K-1), and the exact (t=0) parent is
[
h=2d-4p-K-4.
]
Its normalized height is
[
rac hp=\frac{124-64x-(5K+10)/p}{9},
]
so (2p<h<3p), which is the even-parent gap between scales (K-2) and (K-1). Since (3\mid d), (p\equiv2\pmod3), and (K\equiv0\pmod3), we have (h\equiv0\pmod3), hence (2h+5\not\equiv0\pmod3). Thus (h) is parentless. The (t=1) (or (t=2)) gap arguments in the existing notes remain useful, but the correct conclusion is that the omitted (t=0) parent is parentless—not that (E) has no odd parent.

## 3. The high-(Y) third-lift cases have a genuine (t=0) parent

In the exceptional (X\equiv3\pmod9) phase, let
[
h=2(X/3)-4p-K-4,qquad Y=2h+5.
]
For either non-high third-lift class, (v_3(Y)=2). The (t=0) candidate (g=Y/3) is odd, and
[
rac gp=\frac{248-128x+(25-10K)/p}{27}.
]
For (x\in\mathcal W) and (K\ge266),
[
\frac32<\frac gp<\frac74<2.
]
Thus (g) is in the odd source band at scale (K-2), and
[
G=2g-2p-K-3
]
is a genuine odd ResetParent of (h). The existing bound
[
\frac Gp=\frac{442-256x}{27}-\frac{47K+31}{27p}
]
puts (p<G<3p/2), so (G) has no even parent. But (3\mid g) implies (G\equiv2\pmod3), hence (3\mid Z:=2G+5). The t=1 gap for the parameter (2g) does not eliminate this t=0 parent (G). Therefore the statement that (h) is parentless in the high-(Y) non-high third-lift classes is false.

The next exact odd-parent candidates of (G) use
[
q_t=2^t Z/3^{t+1},qquad t=0,\ldots,v_3(Z)-1.
]
For (q_0=Z/3),
[
\frac{q_0}{p}
=\frac{884-512x+(73-94K)/p}{81}.
]
Its range straddles (3/4). The boundary case (q_0/p=3/4) is not covered by the adjacent t=0 and t=1 bands and needs separate treatment. If (q_0/p>3/4), the t=0 source band at scale (K-3) is available. If (q_0/p<3/4) and (v_3(Z)\ge2), then
[
\frac{q_1}{p}=\frac23\frac{q_0}{p}
]
lies in the scale-((K-4)) odd band ((3/8,1/2)). If (q_0/p<3/4) and (v_3(Z)=1), there is no odd parent of (G). For larger (v_3(Z)), additional separated values of (t) may enter further dyadic bands; no maximal-(t) shortcut is valid.

## 4. A further exact 486-shift law

On this branch define (Z(K)=2G(K)+5). With (e=K+4-a), (e) is even. Since (2^{486}\equiv1\pmod{729}),
[
egin{aligned}
T(K+486)-T(K)
&\equiv972-1944\cdot2^e\pmod{729}\
&\equiv243-486\equiv486\pmod{729}.
end{aligned}
]
Dividing through the definitions (X=T/3), (h=2(X/3)-4p-K-4), (Y=2h+5), (g=Y/3), (G=2g-2p-K-3), gives
[
X(K+486)\equiv X(K)+162\pmod{243},
]
[
h(K+486)\equiv h(K)+27\pmod{81},quad
Y(K+486)\equiv Y(K)+54\pmod{81},
]
[
g(K+486)\equiv g(K)+18\pmod{27},quad
G(K+486)\equiv G(K)+9\pmod{27},
]
and therefore
[
\boxed{Z(K+486)\equiv Z(K)+18\pmod{27}.}
]
This is an exact algebraic lift law. If (9\mid Z(K)), the three lifts (K,K+486,K+972\) cycle through (Z\bmod27=0,18,9) in some order. The law does not itself close the resulting parent branches.

## 5. Exact finite source-parent examples

For (a=15), the interval (mathcal W) contains four non-high high-(Y) candidates:
(K=25815,25977,26301,26463). Exact BigInt enumeration of every (t<v_3(2u+5)) under the full ResetParent grammar gives unique chains:

| (K) | parent-type/scale sequence from (E) | terminal (u/p) |
|---:|---|---:|
| 25815 | odd (t=0,k=K-1); odd (t=0,k=K-2); odd (t=0,k=K-3); even (k=K-3); even (k=K-3) | 0.621913 |
| 25977 | odd (t=0,k=K-1); odd (t=0,k=K-2); odd (t=0,k=K-3); even (k=K-3) | 0.560956 |
| 26301 | odd (t=0,k=K-1); odd (t=0,k=K-2); odd (t=0,k=K-3) | 0.530478 |
| 26463 | odd (t=0,k=K-1); odd (t=0,k=K-2); odd (t=1,k=K-4); even (k=K-4) | 0.373971 |

Every terminal in this finite list is parentless under the exact grammar. These examples are computational evidence only; they do not establish a uniform family theorem. They demonstrate concretely that the omitted lower-(t) branches can be real and may continue through several further resets.

## Consequence for the existing 79/81 statement

The (X\equiv0\pmod9) part can be repaired using Section 2. The high-(Y) non-high third-lift part is not established by the current t=1 gap: it has the genuine t=0 parent (G), and the full set of lower-(t) parents of (G) remains to be closed. The 79/81 count should remain a paper-level conjectural reduction until this branch is handled against the exact ResetParent relation.
