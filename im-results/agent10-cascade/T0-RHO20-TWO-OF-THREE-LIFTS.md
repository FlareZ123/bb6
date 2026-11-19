# Rho-20 phase: exact-valuation lifts and the full inverse-parent fan

**Status (19 November 2026).** The exact identity, 3-adic lift law, valuation-sibling calculations, and logarithmic gap-density calculation below are valid. The previous conclusion that the rho-20 phase is root-excluded in 80 of 81 residue classes is withdrawn. The argument examined only the maximal 3-adic exponent \(t=v_3(X)-1\), but the source-exact odd-parent rule permits every smaller exponent too: it requires \(d\) odd, not \(3\nmid d\). In fact, every rho-20 candidate has an additional \(t=0\) odd parent at level \(K-1\). The higher-valuation calculations therefore classify individual parent choices; they do not exclude the candidate from the inverse tree.

The eight non-rho-20 phases of the original eight-of-nine theorem are unaffected. The rho-20 phase is not fully resolved: for every a divisible by 54, a selected K has a unique complete inverse-parent chain ending in a non-root leaf, excluding an infinite subfamily of candidate fatal heights. Other rho-20 parameters remain open. The general construction below also gives arbitrarily long same-level even-parent chains.

## 1. Setup and source-exact parent rule

Let \(a\ge18\) be even, \(K\ge266\), \(K\equiv2\pmod6\), and
\[
x=\frac{2K+7}{2^a}\in\left[\frac{97}{64},\frac{13}{8}\right],
\qquad
\rho=K+6a\equiv20\pmod{54}.
\]
Write
\[
p=2^K,\quad r=K+4-a,\quad B=(2K+7)2^r,
\]
\[
D=\frac{B-16p+2K+1}{3},\quad E=8p+K-D,\quad X=2E+5.
\]
The exact identity and interval estimate are
\[
3X+2B=80p+2K+13, \tag{1}
\]
\[
\frac{28}{3}<\frac Xp<\frac{65}{6}. \tag{2}
\]
The rho-20 phase table gives \(9\mid X\).

For an odd ResetParent of a target \(u\), the source-exact grammar permits any \(t\ge0\) and odd \(d\) satisfying
\[
2u+5=3^{t+1}d,\qquad
6\cdot2^k+1\le 2^td\le8\cdot2^k-1,
\]
with parent
\[
h=2^{t+1}d-8\cdot2^k-k-5.
\]
There is no condition \(3\nmid d\). Thus, if \(3^n\mid 2u+5\), all exponents \(0\le t<n\) must be considered. Restricting to the maximal exponent \(t=n-1\) does not enumerate all odd parents.

## 2. A guaranteed \(t=0\) parent for every rho-20 candidate

Since \(9\mid X\), put \(P_0=X/3\). From (2),
\[
\frac{28}{9}<\frac{P_0}{p}<\frac{65}{18}.
\]
The endpoints satisfy \(3<28/9\) and \(65/18<4\), so
\[
3p<P_0<4p.
\]
As \(P_0\) is an integer,
\[
3p+1\le P_0\le4p-1.
\]
But this is exactly the odd-source band at level \(k=K-1\):
\[
6\cdot2^{K-1}+1=3p+1
\le P_0\le
4p-1=8\cdot2^{K-1}-1.
\]
Also \(P_0\) is odd because \(X\) is odd. Define
\[
h_0=2P_0-4p-K-4.
\]
Then
\[
2E+5=3P_0,\qquad
2P_0=8\cdot2^{K-1}+h_0+(K-1)+5.
\]
Hence
\[
\operatorname{ResetParent}(h_0,E)
\]
holds with \(t=0\), \(d=P_0\), and \(k=K-1\), for **every** rho-20 candidate.

This is the omitted parent branch. In particular, the exact-valuation \(t=1\) gap for \(v_3(X)=2\), and the exact-valuation \(t=2\) leaf calculation for \(v_3(X)=3\), cannot make \(E\) parentless.

The next odd-parent numerator is
\[
X_1=2h_0+5
=4P_0-8p-2K-3
=\frac{248p-8B-10K+25}{9}. \tag{3}
\]
It is itself divisible by \(3\). Indeed, \(P_0=X/3\) is divisible by \(3\), while \(p=2^K\equiv1\pmod3\) and \(K\equiv2\pmod3\); hence
\[
X_1=4P_0-8p-2K-3\equiv0\pmod3.
\]
So \(h_0\) is not an odd-parent leaf either. Whether one of its odd parents is admissible depends on the next source-band tests.

There is also a useful exact location for \(h_0\). Since \(2K+7\) is odd whereas \(97\cdot2^{a-6}\) is even,
\[
x-\frac{97}{64}\ge2^{-a}.
\]
Using
\[
\frac Xp=\frac{80-32x}{3}+\frac{2K+13}{3p}
\]
and \(2K+13<32\cdot2^{K-a}\) for the present range gives \(X/p<21/2\). Together with (2), this yields
\[
\frac{28}{9}<\frac{P_0}{p}<\frac72.
\]
Consequently, for \(K\ge266\),
\[
2p<h_0<3p.
\]
The even-parent target bands adjacent to this interval are
\[
\left[\frac32p-1,\,2p-3\right]\quad(k=K-2),
\qquad
[3p-1,\,4p-3]\quad(k=K-1).
\]
Thus \(h_0\) has no even parent. Its unresolved continuation is entirely through its odd-parent fan, beginning with the numerator \(X_1\) in (3).

The \(t=0\) parent of \(h_0\) at level \(K-2\), when it exists, is controlled by
\[
\frac{X_1}{3p}
=\frac{248-128x}{27}+\frac{-10K+25}{27p}.
\]
It is admissible precisely when
\[
\frac32p+1\le\frac{X_1}{3}\le2p-1.
\]
Other exponents \(t>0\) must also be checked.

## 3. What the exact-valuation lift calculations do prove

For \(K\mapsto K+54\), the exact identity (1) and \(2^{54}\equiv1\pmod{81}\) give
\[
X(K+54)\equiv X(K)+18\pmod{27}. \tag{4}
\]
The three lifts of a rho-20 class modulo \(54\) therefore have \(X\)-residues \(0,9,18\pmod{27}\), in some order. Exactly two have \(v_3(X)=2\); one has \(27\mid X\).

If \(v_3(X)=2\), the maximal-exponent source coordinate is
\[
P_1=\frac{2X}{9},
\qquad
\frac{56}{27}<\frac{P_1}{p}<\frac{65}{27}.
\]
It lies strictly between \(2p\) and \(3p\), so there is no odd parent with exponent \(t=1\). But \(P_0=(3/2)P_1\) lies in the \(t=0\) band \((3p,4p)\), giving the parent from Section 2. Thus the \(t=1\) gap is a branch-specific statement, not a root exclusion.

For the unique lift with \(27\mid X\), the next shift satisfies
\[
X(K+162)\equiv X(K)+54\pmod{81}. \tag{5}
\]
Among its three lifts, one has \(81\mid X\), and two have \(v_3(X)=3\). For \(v_3(X)=3\), the maximal-exponent coordinate is
\[
P_2=\frac{4X}{27},
\qquad
\frac{112}{81}<\frac{P_2}{p}<\frac{130}{81}.
\]
When this coordinate lies in the \(k=K-2\) odd-source band, the corresponding \(t=2\) parent has no even parent and no odd parent of its own; that particular branch is a leaf. The \(t=1\) coordinate \((3/2)P_2\) lies in the gap \((2p,3p)\). Nevertheless,
\[
P_0=\frac X3=\frac94P_2
\]
lies in the \(k=K-1\) band \((3p,4p)\), so the \(t=0\) parent of \(E\) still exists. The \(t=2\) leaf does not exclude \(E\).

More generally, for \(n\ge2\) put
\[
\Delta_n=2\cdot3^{n+1}.
\]
LTE gives \(2^{\Delta_n}\equiv1\pmod{3^{n+2}}\). Substitution into (1) yields
\[
X(K+\Delta_n)-X(K)
\equiv(4-8\cdot2^r)3^n\pmod{3^{n+1}}. \tag{6}
\]
Since \(r\) is even, the coefficient is \(2\pmod3\), a unit. Thus every three-way lift of a class with \(3^n\mid X\) has one child with higher valuation and two exact-valuation siblings. This lift law is correct, but it describes the maximal-exponent branch only; it does not eliminate lower exponents.

The interval
\[
\frac{28}{9}\left(\frac23\right)^t
<
\frac{P_t}{p}
<
\frac{65}{18}\left(\frac23\right)^t
\]
has logarithmic width \(\log_2(65/56)\). The phase
\[
\log_2(28/9)+t\log_2(2/3)\pmod1
\]
is equidistributed, so a proportion
\[
\log_2(84/65)\approx0.36995
\]
of valuation indices have their **maximal-exponent** source-coordinate interval wholly inside a dyadic gap. This is a density statement about exact-valuation source coordinates, not about parentless candidates: lower exponents \(s<t\) have
\[
P_s=\left(\frac32\right)^{t-s}P_t,
\]
and may land in other source bands. In the rho-20 family the \(s=0\) band is always present.

## 4. An explicit unbounded same-level even-parent chain

The guaranteed \(t=0\) parent gives more than an omitted edge. It yields a family with arbitrarily many successive even parents at one fixed level.

For each even \(a\ge18\), let
\[
K_{\min}=\frac{97\cdot2^{a-6}-6}{2},
\]
and choose the least \(\delta\in\{0,\ldots,53\}\) such that
\[
K_a=K_{\min}+\delta\equiv20-6a\pmod{54}.
\]
Then
\[
2K_a+7=97\cdot2^{a-6}+1+2\delta,
\qquad
x=\frac{97}{64}+\frac{1+2\delta}{2^a}.
\]
For \(a\ge18\), this lies in the required \(x\)-interval, \(K_a\equiv2\pmod6\), and \(\rho=20\pmod{54}\).

Write \(p=2^{K_a}\), and form \(E_0=E\), \(X_0=2E_0+5\). The \(t=0\) parent at level \(K_a-1\) is \(E_1=h_0\). Put \(X_1=2E_1+5\). Equation (3) becomes
\[
\frac{X_1}{p}
=
6-\frac{128(1+2\delta)}{9\cdot2^a}
-\frac{10K_a-25}{9p}.
\]
For \(a\ge18\), this lies strictly between \(5\) and \(6\). Therefore \(P_1=X_1/3\) lies in the odd-source band at level \(K_a-2\), giving a second \(t=0\) parent
\[
y_0=2P_1-2p-K_a-3.
\]
Set \(L=K_a-2\) and \(D_0=2p-y_0\). Direct substitution gives
\[
D_0=
\frac{256(1+2\delta)2^{K_a-a}+47K_a+31}{27},
\]
and hence
\[
D_0+L=
\frac{256(1+2\delta)2^{K_a-a}+74K_a-23}{27}
<1024\cdot2^{K_a-a}. \tag{7}
\]
The last inequality follows from \(\delta\le53\) and \(74K_a-23<2^{K_a-a}\) in this range.

Now define
\[
D_{j+1}=2D_j+L,\qquad y_j=2p-D_j.
\]
Then
\[
D_j=2^j(D_0+L)-L.
\]
For every \(0\le j\le a-11\), (7) gives
\[
D_j\le2^j(D_0+L)
\le2^{a-11}\cdot1024\cdot2^{K_a-a}
=2^{K_a-1}=\frac p2.
\]
Also \(D_j\ge D_0\ge3\). Thus
\[
\frac32p\le y_j\le2p-3,
\]
which is exactly inside the even-parent target band at level \(L=K_a-2\):
\[
6\cdot2^L-1\le y_j\le8\cdot2^L-3.
\]
Each \(y_j\) therefore has an even parent
\[
y_{j+1}=2y_j-2p-L.
\]
There are at least \(a-10\) successive same-level even-parent edges after the two initial odd \(t=0\) edges. Since \(a\) is unbounded, this gives arbitrarily deep finite inverse paths in the rho-20 family. It is a reverse-graph result, not a proof that any path reaches the blank root.

Exact witnesses from the construction:
- \(a=18\): \(K_a=198686\), \(\delta=33\), at least \(8\) same-level even edges.
- \(a=20\): \(K_a=794672\), \(\delta=51\), at least \(10\) same-level even edges.
- \(a=22\): \(K_a=3178544\), \(\delta=51\), at least \(12\) same-level even edges.

## 5. An infinite rho-20 subfamily has a unique parent chain

A useful specialization makes the entire inverse fan, not just one branch, explicit. Let \(a\ge54\) be divisible by \(54\), and set
\[
K=97\cdot2^{a-7}+30.
\]
Then
\[
2K+7=97\cdot2^{a-6}+67,\qquad
x=\frac{97}{64}+\frac{67}{2^a}.
\]
This lies in the required interval. Direct modular arithmetic gives
\[
K\equiv20\pmod{54},\qquad K\equiv20\pmod{81},
\]
so \(K\equiv2\pmod6\) and \(\rho=K+6a\equiv20\pmod{54}\). Also
\[
r=K+4-a\equiv24\pmod{54}.
\]
Consequently,
\[
p=2^K\equiv2^{20}\equiv31\pmod{81},\qquad
B=(2K+7)2^r\equiv47\cdot2^{24}\equiv65\pmod{81}.
\]
Using (1) and (3),
\[
3X=80p+2K+13-2B\equiv54\pmod{81},
\]
\[
9X_1=248p-8B-10K+25\equiv27\pmod{81}.
\]
Therefore
\[
X\equiv18\pmod{27},\quad v_3(X)=2,
\qquad
X_1\equiv3\pmod9,\quad v_3(X_1)=1. \tag{8}
\]

The target \(E\) has no even parent: from the definitions,
\[
E=\frac{40p+K-B-1}{3},\qquad
\frac Ep=\frac{40-16x}{3}+\frac{K-1}{3p},
\]
which lies strictly between \(4\) and \(6\). Its only possible odd exponents are \(t=0,1\), since \(v_3(X)=2\). The \(t=1\) coordinate \(2X/9\) lies in \((2p,3p)\), a dyadic source gap, while \(t=0\) gives the parent \(h_0\) from Section 2. Thus \(h_0\) is the unique parent of \(E\).

The state \(h_0\) has no even parent by Section 2. By (8), its odd numerator \(X_1=2h_0+5\) has valuation exactly one, so only \(t=0\) is possible. Moreover,
\[
\frac{X_1}{p}
=6-\frac{128\cdot67}{9\cdot2^a}-\frac{10K-25}{9p}
\]
lies strictly between \(5\) and \(6\). Hence \(P_1=X_1/3\) lies in the odd-source band at level \(K-2\), and \(h_0\) has the unique parent
\[
y_0=2P_1-2p-K-3.
\]

Put \(L=K-2\) and \(D_0=2p-y_0\). Exact substitution gives
\[
D_0=\frac{17152\cdot2^{K-a}+47K+31}{27},
\qquad
D_0+L=\frac{17152\cdot2^{K-a}+74K-23}{27}. \tag{9}
\]
Define
\[
D_{j+1}=2D_j+L,\qquad y_j=2p-D_j.
\]
Then
\[
D_j=2^j(D_0+L)-L,
\]
and for \(j\le a-10\),
\[
\frac{D_j}{p}
=\frac{17152}{27\cdot2^{a-j}}
+\frac{2^j(74K-23)}{27p}-\frac Lp.
\]
The absolute value of the last two terms is less than \(K^2/2^K<1/100\): use \(2^a<2K+7\), \(j\le a-10\), and \(K\ge266\). In particular,
\[
\frac{D_{a-11}}p=\frac{67}{216}+\varepsilon_{a-11}<\frac12,
\qquad
\frac{D_{a-10}}p=\frac{67}{108}+\varepsilon_{a-10}\in\left(\frac12,1\right),
\]
where \(|\varepsilon_j|<1/100\). Also \(D_0\ge3\), and \(D_j\) increases with \(j\). Therefore, for \(0\le j\le a-11\),
\[
\frac32p\le y_j\le2p-3,
\]
so \(y_j\) has its even parent at level \(L\), namely
\[
y_{j+1}=2y_j-2p-L.
\]
There are exactly \(a-10\) such even-parent edges. At the next state,
\[
\frac{D_{a-10}}p\in(1/2,1)
\quad\Longrightarrow\quad
p<y_{a-10}<\frac32p.
\]
This is the gap between the adjacent even-parent bands, so \(y_{a-10}\) has no even parent.

There are no odd parents anywhere on this even chain. From \(X_1\equiv3\pmod9\), \(P_1=X_1/3\equiv1\pmod3\), and therefore
\[
y_0=2P_1-2p-K-3\equiv1\pmod3.
\]
Since \(p\equiv1\pmod3\) and \(L=K-2\equiv0\pmod3\), the recurrence gives
\[
y_{j+1}\equiv2y_j-2p-L\equiv1-y_j\pmod3.
\]
Thus \(y_j\) alternates between residues \(1\) and \(0\), never \(2\). An odd parent requires \(3\mid2y_j+5\), equivalently \(y_j\equiv2\pmod3\), so no odd parent exists, including at the terminal gap state.

The complete inverse-parent graph of \(E\) is therefore a single chain: \(E\) has only \(h_0\); \(h_0\) has only \(y_0\); the \(y_j\) have only the displayed even parent until \(y_{a-10}\), which is a non-root leaf. Hence \(E\) is not in the blank-root ResetChain. This proves an infinite subfamily of rho-20 candidate fatal heights is unreachable from the blank root. It does **not** exclude the remaining rho-20 parameters or prove #746 nonhalting.

## 6. Finite exact parent-fan census at \(a=18\)

A BigInt enumerator in rho20_parent_census.mjs checks every even and odd ResetParent choice for every rho-20 candidate in the \(a=18\) interval. It enumerates every odd exponent \(0\le t<v_3(2u+5)\), not only the maximal exponent, and uses the unique possible dyadic level determined by the source value's bit length.

There are \(265\) candidate \(K\)-values. Their exact root numerators have valuation histogram
\[
v_3(X)=2:177,\quad3:59,\quad4:19,\quad5:7,\quad6:2,\quad10:1.
\]
All \(265\) computed parent graphs terminate without reaching \(2\); the maximum graph depth is \(12\), the maximum node count is \(18\), and \(90\) graphs contain a branching node. This is a finite census only, not a proof for other \(a\). The script is provided so future work can reproduce and extend it.

## 7. Correct scope and next target

- The original eight non-rho-20 phases remain paper-level root-leaf exclusions. In the modulo-\(486\) refinement they account for \(8\cdot9=72\) of the \(81\) residue classes.
- The rho-20 phase is **not fully excluded**. Every candidate has the t=0 parent at level K-1, so the previous 80/81 claim is withdrawn. The infinite subfamily a≡0 (mod 54), K=97·2^(a-7)+30 is excluded by its unique inverse chain, but all other rho-20 parameter classes remain open.
- The exact-valuation lift law and gap-density calculation remain valid as statements about individual parent choices, but do not prove parentlessness.
- The next mathematical task is the complete odd/even parent fan of \(h_0\), including the transitions out of the same-level even chain and the higher-exponent odd branches. The finite census and the unbounded-chain construction are useful guides, not substitutes for an all-parameter proof.

Nothing here determines #746's all-time blank-root reachability or BB(6).
