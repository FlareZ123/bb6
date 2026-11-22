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
There is no condition (3\nmid d). If (v_3(2u+5)=r), every (t=0,1,ldots,r-1) is an algebraic candidate; each must be tested against its own dyadic source band. A gap for the maximal-(t) candidate does not exclude the lower-(t) candidates. The existing [NESTED-ODD-PARENT-HENSEL.md](NESTED-ODD-PARENT-HENSEL.md) develops arbitrary finite-depth odd-parent chains for a different U/Q family using this same non-primitive-quotient feature; it is a warning against inferring termination from a few lifts, not a proof about the present K3 family.

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

## 4. A 3-adic isometry for the G-numerator

On this branch define
[
Z(K)=2G(K)+5.
]
Let (s\ge0) and (Delta=486\cdot3^s=2\cdot3^{s+5}). Since the order of 2 modulo (3^{s+6}) divides (2\cdot3^{s+5}),
[
2^{K+\Delta}\equiv2^K,qquad
2^{K+4-a+\Delta}\equiv2^{K+4-a}
pmod{3^{s+6}}.
]
The linear terms in (T) therefore give
[
egin{aligned}
T(K+\Delta)-T(K)
&\equiv 2\Delta-4\Delta\,2^{K+4-a}
\pmod{3^{s+6}}\\
&=(4-8\cdot2^{K+4-a})3^{s+5}
\equiv2\cdot3^{s+5}
\pmod{3^{s+6}},
end{aligned}
]
because (K+4-a) is even and (2^{K+4-a}\equiv1\pmod3).

Dividing successively through (X=T/3), (h=2(X/3)-4p-K-4), (Y=2h+5), (g=Y/3), (G=2g-2p-K-3), and (Z=2G+5), with the branch divisibilities (3\mid X) and (9\mid Y), yields
[
X(K+\Delta)\equiv X(K)+2\cdot3^{s+4}\pmod{3^{s+5}},
]
[
h(K+\Delta)\equiv h(K)+3^{s+3}\pmod{3^{s+4}},
quad
Y(K+\Delta)\equiv Y(K)+2\cdot3^{s+3}\pmod{3^{s+4}},
]
[
g(K+\Delta)\equiv g(K)+2\cdot3^{s+2}\pmod{3^{s+3}},
quad
G(K+\Delta)\equiv G(K)+3^{s+2}\pmod{3^{s+3}},
]
and hence
[
oxed{Z(K+486\cdot3^s)\equiv
Z(K)+2\cdot3^{s+2}\pmod{3^{s+3}}.}
	ag{10}
]
The (s=0) case is the earlier (486)-shift law.

Now fix a high-(Y) residue class (K\equiv K_0\pmod{486}) with (9\mid Z(K_0)), and write (K=K_0+486m). The shift law gives
[
\Phi(m+3^s)-\Phi(m)\equiv2\cdot3^s\pmod{3^{s+1}},
qquad
\Phi(m):=Z(K_0+486m)/9.
]
Thus (Phi) is a 3-adic isometry: for every (r\ge1), each target residue modulo (3^r) has a unique preimage residue (m\bmod3^r). In particular, for every fixed (r), there is one cylinder on which
[
3^{r+2}\mid Z(K_0+486m).
]
This proves unbounded 3-adic valuation along the (K_0\bmod486) progression, conditional on the base class (9\mid Z(K_0)). It is not a ResetParent-chain or blank-root-reachability conclusion by itself.

For fixed (r), the dyadic window (mathcal W) contains representatives of any such (K\bmod(486\cdot3^r)) cylinder once
[
\frac{53}{2048}2^a>486\cdot3^r.
]
This is eventually true as odd (a\to\infty). To use the isometry in a source-parent construction, one must still select a valuation (t) and a dyadic source band simultaneously; the existing five-point band lemma in [NESTED-ODD-PARENT-HENSEL.md](NESTED-ODD-PARENT-HENSEL.md) is a possible tool, but its recursive hypotheses have not yet been established for this K3 family.

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
