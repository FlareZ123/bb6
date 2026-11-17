# Infinite t=0 fatal family excluded by a unique odd-parent leaf

**Status:** exact paper derivation over the source-certified reset inverse/root-chain semantics. The new infinite-family arithmetic is not yet Lean-formalized, so this remains in \`im-results/\`. It is not a global nonhalting proof.

## Theorem

There are infinitely many t=0 adjacent-fatal source candidates \(E\) for which
\[
\neg\operatorname{ResetChain}(2,E).
\]
For every member of this family:

1. \(E\) has no even \(\operatorname{ResetParent}\).
2. \(E\) has exactly one odd \(\operatorname{ResetParent}\), namely \(h'\) at level \(L=K-1\).
3. \(h'\) has no \(\operatorname{ResetParent}\) of either parity.

Thus \(E\) is not reachable from the blank reset root. The associated t=0 fatal tail cannot occur on the blank-root trajectory. This excludes an infinite subfamily of candidate fatal histories, not all possible halting histories of machine #746.

The proof uses the exact two-arm \(\operatorname{ResetParent}\) definition in [FirstInverseComplete.lean](FirstInverseComplete.lean) and the root-chain equivalence in [ResetChain.lean](ResetChain.lean). It does **not** rely on the still-uncompiled t=0 even-parent branch draft.

## Infinite parameter family and fatal source

Take
\[
a=18n\quad(n\ge1),\qquad K\equiv38\pmod{54},
\qquad
\frac{309}{200}\le x:=\frac{2K+7}{2^a}\le\frac{31}{20}.
\tag{1}
\]
For each \(a=18n\), the eligible \(K\)-interval has length \(2^a/400>54\), so it contains an integer in the residue class \(38\bmod54\). Hence infinitely many pairs \((a,K)\) exist. They all have \(K\ge266\).

Put
\[
p=2^K,\quad c=2K+7,\quad r=K+1-a,\quad B_0=c\,2^{r+3},
\]
and
\[
D_0=\frac{B_0-16p+2K+1}{3},\qquad E=8p+K-D_0.
\tag{2}
\]
Here \(K\equiv2\bmod6\), \(a\) is even, \(r\) is odd, and \(a=\lfloor\log_2 c\rfloor\). Also \(4c\le7\cdot2^a\), since \(x\le31/20<7/4\). The fatal-source equation is
\[
B_0=40p+K-1-3E.
\tag{3}
\]
The numerator defining \(D_0\) is divisible by \(3\): modulo \(3\), \(c\equiv2\), \(2^{r+3}\equiv1\), \(16p\equiv1\), and \(2K+1\equiv2\).

Since \(B_0=16xp\), the interval in (1) puts \(B_0\) strictly inside
\[
16p+4K+20\le B_0\le28p+4K+8.
\]
Equivalently, the t=0 raw odd-source parameter
\[
d_0=4p+\frac{E+K+5}{2}
\]
satisfies \(6p+1\le d_0\le8p-1\). Equation (3), with \(16\mid B_0\), gives \(E+K\equiv1\bmod4\), so this is a genuine odd-exit source. The same interval gives
\[
4p-K-3\le E\le8p-K-7,
\]
which certifies \(\operatorname{FirstFailureAt}(E,K)\).

## Exact odd parent of E

The residues are
\[
2^a\equiv1\pmod{27},\quad
K\equiv11\pmod{27},\quad
K+4-a\equiv6\pmod{18},\quad
2^{K+4-a}\equiv10\pmod{27}.
\]
Using
\[
3D_0=(c-2^a)2^{K+4-a}+2K+1,
\]
we obtain
\[
3D_0\equiv(2-1)\cdot10+23\equiv6\pmod{27},
\]
hence \(D_0\equiv2\bmod9\). Also
\[
A:=16p+2K+5\equiv1\pmod9,\qquad
X:=2E+5=A-2D_0\equiv6\pmod9.
\tag{4}
\]
Therefore \(v_3(X)=1\) exactly. Set
\[
P=X/3.
\]
Then \(P\) is odd. Direct substitution gives
\[
\frac{P}{p}
=\frac{80-32x+(2K+13)/p}{9}.
\tag{5}
\]
For the interval (1), and \(K\ge266\), this lies strictly between \(3\) and \(4\). Thus, with \(L=K-1\),
\[
6\cdot2^L+1\le P\le8\cdot2^L-1.
\tag{6}
\]
Define
\[
h'=2P-8\cdot2^L-L-5.
\tag{7}
\]
Then
\[
2P=8\cdot2^L+h'+L+5,\qquad 2E+5=3P.
\]
Together with (6), these are exactly the odd arm of \(\operatorname{ResetParent}(h',E)\), with \(t=0\).

This odd parent is unique. Any odd parent of \(E\) has
\[
2E+5=3^{t+1}d.
\]
By (4), \(v_3(2E+5)=1\), so \(t=0\) and \(d=P\). The odd source bands \([6\cdot2^j+1,8\cdot2^j-1]\) are pairwise disjoint, and (6) places \(P\) in the unique band \(j=L\). The source equation then forces the parent height to be exactly \(h'\).

## E has no even parent

From (2),
\[
\frac{E}{p}
=8-\frac{16}{3}(x-1)+\frac{K-1}{3p}.
\]
The interval (1) gives
\[
5<\frac{E}{p}<\frac{407}{75}<\frac{11}{2}.
\tag{8}
\]
An even parent at level \(j\) would require
\[
6\cdot2^j-1\le E\le8\cdot2^j-3.
\]
For \(j\le K-1\), the upper bound is at most \(4p-3<E\). For \(j\ge K\), the lower bound is at least \(6p-1>E\), by (8). Hence \(E\) has no even parent. Its unique parent of either parity is \(h'\).

## h' has no parent

First, (4) gives \(P\equiv2\bmod3\). Since \(L=K-1\equiv1\bmod6\),
\[
h'=2P-8\cdot2^L-L-5\equiv0\pmod3.
\tag{9}
\]
Every odd-parent output \(u\) satisfies \(2u+5=3^{t+1}d\), hence \(u\equiv2\bmod3\). Equation (9) therefore excludes every odd parent of \(h'\).

For even parents, put
\[
\epsilon=\frac{2K+13}{p},\qquad
\eta=\frac{L+5}{2^L}.
\]
Equations (5) and (7) yield
\[
\frac{h'}{2^L}
=\frac{248-128x+4\epsilon}{9}-\eta.
\tag{10}
\]
For \(K\ge266\), \(\epsilon<1/100\) and \(\eta<1/100\). Using (1) in (10),
\[
\frac{248}{45}-\frac1{100}
<
\frac{h'}{2^L}
<
\frac{1256}{225}+\frac1{225}
=\frac{419}{75}
<6.
\]
The lower bound is greater than \(11/2\). Thus
\[
\frac{11}{2}\,2^L<h'<\frac{419}{75}\,2^L<6\cdot2^L.
\tag{11}
\]
An even parent at level \(j\le L-1\) has target at most \(4\cdot2^L-3<h'\). An even parent at level \(j\ge L\) has target at least \(6\cdot2^L-1>h'\), using (11) and \((6-419/75)2^L>1\). So \(h'\) has no even parent either.

Combining (9) and (11), \(h'\) has no \(\operatorname{ResetParent}\) at all.

## Root nonreachability

The exact source theorem \(\operatorname{root\_reset\_chain\_iff}\) identifies blank-root reachability with finite \(\operatorname{ResetParent}\)-chains from \(2\). If \(E\) were root-reachable, its last predecessor would have to be its unique parent \(h'\). But \(h'\ne2\) and has no parent, so no such chain can exist:
\[
\neg\operatorname{ResetChain}(2,E).
\]
Therefore the t=0 fatal-source configuration \(E\), and its associated fatal tail, are excluded from the blank-root trajectory for every pair in (1).

This is an infinite, root-specific exclusion theorem for one structured family. It does not decide the other t=0 phases, the t=1 or higher-valuation branches, or the global nonhalting question.

## Reproducible instance

The accompanying BigInt script checks
\[
a=18,\quad K=202538,\quad r=202521,\quad L=202537.
\]
It verifies the exact divisibilities, source bands, the unique odd parent, the mod-3 parentless condition, both dyadic gaps excluding even parents, and all displayed first-failure endpoint inequalities.

Run:
\`\`\`bash
node im-results/agent10-cascade/t0_infinite_synthetic_odd_parent_family.mjs
\`\`\`
