# Infinite synthetic odd-parent family for the t=0 adjacent-fatal entry

**Status:** exact arithmetic construction; not a blank-root reachability result and not Lean-verified. This belongs in \`im-results/\`, not \`results/\`.

## Result

There are infinitely many levels \(K\ge266\) for which the special \(t=0,\ L=K+1\) adjacent-fatal source candidate has a genuine odd immediate \`ResetParent\` from level \(K-1\), with no intervening even resets at level \(K\) (\(q=0\)) and incoming odd-parent valuation \(t=0\).

Thus the local inverse grammar does not eliminate this fatal family by parent nonexistence. The remaining question is whether the explicitly constructed parent is the actual blank-root state at that level. No root path is asserted.

## Infinite parameter family

Take
\[
a=18n\quad(n\ge1),\qquad K\equiv38\pmod{54},
\qquad
\frac{29}{20}\le x:=\frac{2K+7}{2^a}\le\frac{31}{20}.
\tag{1}
\]
For each \(a=18n\), the interval of eligible \(K\) has length \(2^a/20>54\), so it contains an integer congruent to \(38\bmod54\). Hence there are infinitely many pairs \((a,K)\). In particular \(K\ge266\).

Put
\[
p=2^K,\quad c=2K+7,\quad r=K+1-a,\quad
B_0=c\,2^{r+3},
\]
and define
\[
D_0=\frac{B_0-16p+2K+1}{3},
\qquad h=8p+K-D_0.
\tag{2}
\]
Here \(K\equiv2\bmod6\), \(a\) is even, and \(r\) is odd. Also \(2^a\le c<2^{a+1}\) and \(4c\le7\cdot2^a\), since \(1<x\le31/20<7/4\). Thus \(r=K+1-\lfloor\log_2(2K+7)\rfloor\) is exactly the unique t=0 fatal-tail exponent from the source-band characterization.

The fatal-source equation is
\[
B_0=40p+K-1-3h.
\tag{3}
\]
It follows directly from (2). Since \(B_0=16xp\) and \(29/20\le x\le31/20\),
\[
\frac{232}{10}p\le B_0\le\frac{248}{10}p.
\]
For \(K\ge266\), this lies strictly inside
\[
16p+4K+20\le B_0\le28p+4K+8.
\]
Equivalently, the t=0 raw source parameter
\[
d_0=4p+\frac{h+K+5}{2}
\]
lies in its exact band \(6p+1\le d_0\le8p-1\). The congruence \(16\mid B_0\) in (3) also gives \(h+K\equiv1\bmod4\), so this is a genuine odd-exit source. The same interval gives
\[
4p-K-3\le h\le8p-K-7,
\]
which certifies \(\operatorname{FirstFailureAt}(h,K)\): the lower endpoint gives the guard at \(K-1\), all earlier guards follow from the increasing thresholds, and the upper endpoint gives \(h+K+5<8p\).

## Incoming odd parent: exact 3-adic phase

The residues are fixed by the chosen congruence classes:
\[
2^a\equiv1\pmod{27},\quad
K\equiv11\pmod{27},\quad
K+4-a\equiv6\pmod{18},\quad
2^{K+4-a}\equiv10\pmod{27}.
\]
Therefore
\[
3D_0=(c-2^a)2^{K+4-a}+2K+1
\equiv(2-1)\cdot10+23
\equiv6\pmod{27},
\]
so
\[
D_0\equiv2\pmod9.
\tag{4}
\]
For the first level-\(K\) entry \(E=h\), let
\[
A=16p+2K+5,\qquad X=2E+5=A-2D_0.
\]
Since \(K\equiv2\bmod6\), \(2^K\equiv4\bmod9\), and \(2K+5\equiv0\bmod9\). Thus \(A\equiv1\bmod9\), and (4) yields
\[
X\equiv1-4\equiv6\pmod9.
\tag{5}
\]
Consequently \(v_3(X)=1\) exactly. The incoming odd-parent selector forces \(q\) even when \(D_0\equiv2\bmod3\); choose \(q=0\), which is admissible. Then \(E=h\) and
\[
P:=X/3
\]
is an odd integer. Its incoming odd-parent valuation is \(t=v_3(X)-1=0\).

## The dyadic source band is exactly level \(K-1\)

Substituting (2) into \(P=X/3\) gives
\[
\frac{P}{2^K}
=\frac{80-32x+(2K+13)/2^K}{9}.
\tag{6}
\]
For \(29/20\le x\le31/20\), the main term in (6) lies between \(152/45\) and \(56/15\). Since \((2K+13)/2^K<1\) for \(K\ge266\),
\[
3<\frac{P}{2^K}<4.
\]
With \(L=K-1\), this is precisely
\[
6\cdot2^L+1\le P\le8\cdot2^L-1.
\tag{7}
\]

Define the parent height
\[
h'=2P-8\cdot2^L-L-5.
\tag{8}
\]
Equations (7) and (8) give
\[
2P=8\cdot2^L+h'+L+5,\qquad
2E+5=3P.
\]
The first is the odd-reset source equation at level \(L\), and the second is its output equation. Because \(P\) is odd and (7) is the exact odd-parent band, these equations give
\[
\operatorname{ResetParent}(h',E).
\]
They also certify \(\operatorname{FirstFailureAt}(h',L)\): the lower endpoint in (7) implies \(h'\ge4\cdot2^L-L-3\), while the upper endpoint gives \(h'+L+5<8\cdot2^L\); the earlier sweep guards follow from the lower bound. Finally,
\[
2^{K-2}<3^{K-1}=3^L,\qquad t=0\le L,
\]
so the odd-parent scale condition is satisfied as well.

We have therefore constructed an exact local incoming odd parent from level \(K-1\) for every pair in (1). The fatal source at level \(K\) has \(q=0\), and its t=0 fatal-tail equation is (3).

## Reproducible instance

The accompanying BigInt script checks the first concrete instance:
\[
a=18,\quad K=190064,\quad r=190047,\quad L=190063.
\]
It verifies the exact divisibilities, source bands, first-failure endpoint inequalities, and both parent equations without printing the enormous heights.

Run:
\`\`\`bash
node im-results/agent10-cascade/t0_infinite_synthetic_odd_parent_family.mjs
\`\`\`

## Root-facing boundary

This construction proves existence in the *synthetic source grammar*, not in the blank-root reset chain. In particular, \(\operatorname{ResetParent}(h',E)\) does not establish \(\operatorname{ResetChain}(2,h')\). The root-specific task is now sharply stated: exclude these explicit \(h'\) values from the actual root trajectory, or find one that is reached. A proof based only on the absence of a local odd parent cannot settle the t=0 family.
