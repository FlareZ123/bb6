# Fixed-depth U-index Hensel selector

**Status:** The Q-depth selector modules compiled in original-source workflow run 43397274339 with standard axiom output; the integrated workflow then failed at UParentCone887.lean:75 on a bundled ResetParent band argument. That constructor call is patched on branch commit 7e71e610224fd3de2b66816724e7241ee96f3603; a manual rerun is pending. The fixed-depth infinite-arm derivation and the nested cascade in NESTED-ODD-PARENT-HENSEL.md remain mathematical arguments, not Lean-formalized theorems. This note concerns one specific first-tier U/Q ray depth, \(j=3402\), across the family \(n=887+13122r\). It is not a blank-root exclusion or a BB(6) decision.

## 1. The exact numerator

The source-connected Q numerator from QDepthDefs.lean is

\[
Q_j(n)=28\cdot2^n-2n+15-2^{j+4}(2n+3).
\]

On the even spine, the corresponding candidate state is \(z=(Q_j(n)/9-5)/2\), whenever the quotient is integral. The first-tier U branch uses \(j\equiv0\pmod6\); fix \(j=3402\), and put

\[
L=13122=2\cdot3^8,\qquad n(r)=887+Lr,\qquad
F(r)=Q_{3402}(n(r))/3^8.
\]

The base divisibility \(3^8\mid Q_{3402}(887)\) is confirmed by the exact modular census in UIndexHenselCensus.mjs. The branch also contains Lean qDepthResidue_887_table / qDepthResidue_iff declarations for the precision-7 selector \(j=3402\bmod4374\). Agent 44 inspected run 43397274339 and confirmed that QDepthDefs, QDepthLift, QDepthBase, QDepthSelectorBase, QDepthSelector, QDepth887, and QDepthHensel all compiled there with axiom profile \([propext, Classical.choice, Quot.sound]\). The workflow failed only later in UParentCone887.lean:75; the constructor-shape repair is committed but not yet rerun. Do not infer that the complete U-parent cone passed.

## 2. A 3-adic isometry in the family parameter

For every \(m\ge0\),

\[
3^{m+1}\mid 2^{2\cdot3^m}-1.
\]

An elementary induction proves this: the base \(m=0\) is \(3\mid 4-1\); if \(A=2^{2\cdot3^m}\equiv1\pmod{3^{m+1}}\), then
\(A^3-1=(A-1)(A^2+A+1)\), and \(3\mid A^2+A+1\). In particular, \(3^9\mid2^L-1\), so

\[
Q_{3402}(887+Lr)\equiv Q_{3402}(887)\pmod{3^8}
\]

for every \(r\). Thus \(F(r)\) is an integer for every natural \(r\).

For any \(r,s\ge0\) and \(a\in\{0,1,2\}\), direct subtraction gives

\[
\begin{aligned}
Q_{3402}(n(r+a3^s))-Q_{3402}(n(r))
={}&28\cdot2^{n(r)}(2^{L a3^s}-1)\\
&-4(1+2^{3406})\,a\,3^{8+s}.
\end{aligned}
\]

The first term is divisible by \(3^{9+s}\), by the preceding power lemma with \(m=8+s\). Since \(3406\) is even, \(2^{3406}\equiv1\pmod3\), and hence
\(-4(1+2^{3406})\equiv1\pmod3\). Dividing by \(3^8\) yields the exact lift law

\[
\boxed{F(r+a3^s)\equiv F(r)+a3^s\pmod{3^{s+1}}.}
\]

Consequently, among the three lifts \(r,r+3^s,r+2\cdot3^s\) of any residue modulo \(3^s\), exactly one makes \(F\) divisible by \(3^{s+1}\). Starting with the unique class modulo \(1\), there is therefore a unique compatible residue

\[
\rho_s\pmod{3^s}
\quad\text{such that}\quad
3^{8+s}\mid Q_{3402}(887+13122r)
\iff r\equiv\rho_s\pmod{3^s}.
\]

This also proves that \(F:\mathbb Z_3\to\mathbb Z_3\) is a 3-adic isometry: if \(r-r'\) has exact 3-adic valuation \(s\), then so does \(F(r)-F(r')\). In particular, the valuation of this fixed-depth numerator is unbounded as \(r\) varies; every exact valuation \(v_3(Q)=8+s\) occurs on infinitely many natural \(r\).

## 3. Exact initial selector residues

The following residues were computed by exact modular arithmetic; the lift law proves that each listed class is the unique class at its precision.

| \(s\) | Condition | Unique \(r\bmod 3^s\) |
|---:|---|---:|
| 0 | \(3^8\mid Q\) | 0 mod 1 |
| 1 | \(3^9\mid Q\) | 1 mod 3 |
| 2 | \(3^{10}\mid Q\) | 4 mod 9 |
| 3 | \(3^{11}\mid Q\) | 4 mod 27 |
| 4 | \(3^{12}\mid Q\) | 4 mod 81 |
| 5 | \(3^{13}\mid Q\) | 85 mod 243 |
| 6 | \(3^{14}\mid Q\) | 328 mod 729 |
| 7 | \(3^{15}\mid Q\) | 328 mod 2187 |
| 8 | \(3^{16}\mid Q\) | 2515 mod 6561 |
| 9 | \(3^{17}\mid Q\) | 15637 mod 19683 |
| 10 | \(3^{18}\mid Q\) | 35320 mod 59049 |
| 11 | \(3^{19}\mid Q\) | 94369 mod 177147 |

For example:
- \(r=13\) gives \(n=171473\) and \(v_3(Q)=10\), so the maximal odd-parent exponent of \(z\) is \(t=7\);
- \(r=4\) gives \(n=53375\) and \(v_3(Q)=12\), so the maximal exponent is \(t=9\);
- \(r=1057\) gives \(n=13870841\) and \(v_3(Q)=14\), so the maximal exponent is \(t=11\).

In all three cases the maximal odd-parent quotient \(2^t(Q/3^{t+3})\) lies in its required dyadic image band. These are concrete valid high-valuation branches, not merely divisibility candidates.

## 4. Exact reverse-cone experiments

The accompanying UIndexHenselCensus.mjs implements the two exact ResetParent arms from FirstInverseComplete.lean and the same finite predecessor enumeration as ParentsFast.lean. It reproduces the following reverse cones rooted at the candidate \(z=(Q/9-5)/2\):

| \(r\) | \(n\) | \(v_3(Q)\) | maximal \(t\) | nodes | edges | max depth | root 2 present? |
|---:|---:|---:|---:|---:|---:|---:|---|
| 4 | 53375 | 12 | 9 | 21 | 20 | 6 | no |
| 13 | 171473 | 10 | 7 | 17 | 16 | 6 | no |
| 1057 | 13870841 | 14 | 11 | 19 | 18 | 6 | no |

These are exact-integer computational observations only. They are not Lean closedCertFast certificates and do not establish a uniform cone bound. The changing cone sizes and unbounded 3-adic valuation show why the fixed n=887 31-state cone cannot be generalized by simply reusing its finite list.

## 5. Infinitely many valid odd-parent arms (mathematical derivation; not Lean-certified)

The isometry gives more than unbounded divisibility. For every \(t\ge5\), there is a unique class \(r_t\bmod 3^{t-5}\) with \(3^{t+3}\mid Q\). Exactly two of its three lifts modulo \(3^{t-4}\) have \(v_3(Q)=t+3\), and each such class contains arbitrarily large natural \(r\). Thus the maximal odd-parent exponent of \(z\) can be exactly any prescribed \(t\ge5\), on infinitely many indices.

For such an \(r\), put \(d=Q/3^{t+3}\), \(x=2^t d\), and choose an integer \(s\) with
\[
\frac{81}{14}<\frac{2^s}{3^t}<\frac{54}{7}.
\]
Let \(k=n+t-s\). Since \(Q/2^n\to28\) as \(r\to\infty\) along the selected residue class,
\[
\frac{x}{2^k}
=\frac{Q}{2^n}\frac{2^s}{3^{t+3}}
\longrightarrow \frac{28}{27}\frac{2^s}{3^t}\in(6,8).
\]
For sufficiently large \(r\), the exact integer band
\(6\cdot2^k+1\le x\le8\cdot2^k-1\) follows. Then
\[
h=2x-8\cdot2^k-k-5
\]
is positive for large \(k\), and the exact odd-arm equation gives
\(\operatorname{ResetParent}(h,z)\). The first-tier state \(z\) itself is valid for all sufficiently large \(r\): \(Q/2^n\to28\) implies \(z/2^n\to14/9\), inside its scale-\((n-2)\) even band, and its first-tier odd-band quotient \(2(2z+5)=2Q/9\) has ratio tending to \(56/9\in(6,8)\).

There are infinitely many exponents \(t\) admitting such an \(s\). Indeed, the interval for \(2^s/3^t\) has multiplicative width
\((54/7)/(81/14)=4/3\), or logarithmic width \(\log_2(4/3)>0\). Since \(\log_2 3\) is irrational, the fractional parts of \(t\log_2 3\) are dense modulo one; infinitely many \(t\) therefore admit an integer \(s\) in this interval. Combining this with the Hensel classes proves that the fixed depth \(j=3402\) produces infinitely many genuine high-\(t\) odd-parent arms across the family \(n=887+13122r\).

This is a mathematical consequence of the displayed formulas and the standard irrational-rotation density theorem, not a Lean theorem or a blank-root exclusion. It proves that no uniform finite cutoff on the odd exponent \(t\) can close this U branch.

## 6. Exact next-layer numerator and a mod-3 continuation rule

For an odd parent arm of exponent \(t\) and dyadic offset \(\sigma\), let
\[
d=Q/3^{t+3},\quad x=2^t d,\quad k=n+t-\sigma,\quad
h=2x-8\cdot2^k-k-5.
\]
Then \(h\) is the actual predecessor of \(z\) whenever \(x\) is in its odd image band. Direct substitution gives
\[
3^{t+3}(2h+5)=R_{t,\sigma}(n)=A\,2^{n+t-\sigma+4}+Bn+C,
\]
where
\[
A=7\cdot2^\sigma-3^{t+3},\qquad
B=-(2^{t+3}+2^{j+t+7}+2\cdot3^{t+3}),
\]
\[
C=15\cdot2^{t+2}-3\cdot2^{j+t+6}
-3^{t+3}(2t-2\sigma+5).
\]
For even \(j\), \(B\) is a 3-adic unit: the first two powers of 2 differ in exponent by \(j+4\), which is even, so they agree modulo 3 and their sum is nonzero. Thus, once a base divisibility is known, this next-layer numerator has the same one-digit Hensel mechanism along the index progression. It is a natural input to the nested index-selector work; it is not yet formalized here.

There is also an exact first-digit test requiring no large-integer computation. Modulo 3,
\[
2h+5\equiv 2^{t+2}d-(2^k+2k+2)\pmod3.
\]
For \(k\bmod6=0,1\), the second term is 0, so neither exact-Q lift (where \(d\bmod3\in\{1,2\}\)) can make \(3\mid2h+5\). For \(k\bmod6=2,3,4,5\), the second term is a nonzero residue, so exactly one of the two exact-Q lifts has \(3\mid2h+5\). The two lifts give \(d\bmod3=1\) and \(2\), because the Q Hensel digit is a unit.

| \(t\) | \(\sigma\) | \(k\bmod6=5+t-\sigma\) | exact-Q lifts | lift with \(3\mid2h+5\) |
|---:|---:|---:|---|---|
| 7 | 14 | 4 | \(r=13,22\bmod27\) | \(r=13\) |
| 9 | 17 | 3 | \(r=4,166\bmod243\) | \(r=4\) |
| 11 | 20 | 2 | \(r=1057,1786\bmod2187\) | \(r=1786\) |
| 14 | 25 | 0 | \(r=15637,55003\bmod59049\) | neither |

This is only the first digit of the next-layer selector; it does not decide whether the continuing lift has valuation 2, 3, or more. It does, however, prune one of the two exact-Q branches immediately and explains the observed \(v_3(2h+5)\) values in the census.

## 7. Research consequence

The n=887 selector eliminates every \(t\ge5\) first-tier U parent only because its selected depth \(3402\) lies beyond the n=887 spine. Along \(n=887+13122r\), the same depth eventually lies on the spine, and the family-parameter Hensel root produces valid \(t=7,9,11,\ldots\) branches. A proof of global #746 root exclusion must therefore handle this unbounded 3-adic branch, not just the n=887 cone.

The next-layer numerator in Section 6 is not merely a one-off divisibility test. The recursive affine-exponential update preserves a 3-adic unit linear coefficient. The new note [NESTED-ODD-PARENT-HENSEL.md](NESTED-ODD-PARENT-HENSEL.md) uses this to prove arbitrary finite odd-parent inverse depth on positive-density residue classes for each fixed depth, with an explicit five-edge class r=74803 mod177147 and exact band bounds. Its crucial correction is that exact 3-adic valuation is unnecessary for a ResetParent witness: the quotient only needs to remain odd, so the unique next-digit lift that continues the chain may have higher valuation.

This rules out a uniform finite inverse-depth or fixed finite-cone template across this U/Q family. It does not connect any such branch to the authentic blank root. The generic Q-state index selector in Agent 44's PR #95 is complementary and should be integrated rather than duplicated. The next useful formalization is the affine-exponential 3-adic isometry and recursive numerator update, followed by a source-checked four-level ResetParent certificate. Keep all this work in im-results until a root-connected decision is established.
