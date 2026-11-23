# Joint synchronization and square-gap non-closure in original #623 transitions

**Status:** source-faithful, analytically quantified **all-depth counterfamily**. This is a stronger structural no-go than [RobustConeSyncNonclosure.md](RobustConeSyncNonclosure.md): even the **conjunction** of the proposed full-rectangle synchronization invariant and the previously observed old-ray square-gap condition is **not universally forward invariant** in the source-certified canonical cone. Both endpoints use precisely the **same S-window cut**. These are deliberately constructed section states, **not claimed reachable from the blank tape**. The combined all-depth proof uses existing source-certified LE drain facts and exact integer arithmetic; it has not been compiled as one original-source Lean theorem.

## Theorem

Let \(\tau(h)=(3^h-1)/2\). For a state \(D(a,d)\), let \(S=a+d\), \(\ell_S=\min\{h:S+3\le\tau(h)\}\),
\(B=34\ell_S+122\),
\(k=\min\{h:3^h>B\}\),
\(j=\min\{h:3^h>B^3\}\),
\(P=3^{k+2}\),
\(M=3^{j-k-4}\), \(N=M/3\).
For canonical \(p=|a-d|,\ q=\min(a,d)\), write \(g=p-3q\), and on the LE sector let \(h=g-5\). Let \(\operatorname{Sync}_S\) be the exact complete left-and-right carry-rectangle synchronization test of [ExactSynchronizationCriterion.md](ExactSynchronizationCriterion.md).

**For every integer \(\ell\ge30\)**, there is a real, successful original-source #623 accelerated **LE→LE** transition
\[
\boxed{D(4q+c,q)\longrightarrow D(a',d')}
\tag{1}
\]
such that both endpoints satisfy the original source-certified newAffineCone and have the **same** depth \(\ell'_S=\ell_S=\ell\), hence the **same** \(k,j,P,M,N\), while:

1. The input has \(g=c>8q\), so its old-ray square-gap inequality \(h^2>5q\) holds with enormous slack, and its exact S-window word is \((x,y)\in\{(12,1),(13,1)\}\). Both **full** carry rectangles synchronize.
2. The output has **exactly** \(g'=5P\), so \(h'=5P-5\) and
   \[
   \boxed{(h')^2<q'.}
   \tag{2}
   \]
   This violates even the factor-one square-gap condition, let alone the previously observed factor-five bound.
3. Its exact S-window word is \((x',y')\in\{(9,2),(9,3)\}\), which **fails the full left-rectangle synchronization criterion**, because \([x'-3y']_M\in\{3,0\}\), both forbidden.

Thus, even on arbitrary **source-authentic cone-to-cone transitions**, the **joint** predicate
\[
\operatorname{Sync}_S\ \land\ (g-5)^2>5q
\]
is **not inductive**. In the constructed family the *input* has a fixed ratio \(g/q\to9\), whereas the *output* has \(g'/q'\to0\). The target is still separated from the finite logarithmic terminal-danger width by a substantial constant factor: \(g'=5P\) with \(P>9B\). This is not a terminal successor or a blank-root counterexample.

## 1. Choose q so that the full input window has y=1 and the cut does not move

Fix \(\ell\ge30\). Define the proposed common window
\[
B=34\ell+122,\quad k=\min\{i:3^i>B\},\quad
j=\min\{i:3^i>B^3\},
\quad P=3^{k+2},\ M=3^{j-k-4},\ N=M/3,\ H=PN=3^{j-3}.
\]
As \(B\ge1142\), \(k\ge7\) and \(n=j-k-4\ge8\). In particular \(M\ge3^8\), \(N\ge3^7\).

Choose \(t_0\in\{1,3\}\) so that \(1+Mt_0\equiv0\pmod4\). The positive **even** progression
\[
q_r=\frac{3^{k+1}\bigl(1+M(t_0+4r)\bigr)}2,
\quad r=0,1,\ldots
\tag{3}
\]
has step \(G=2H\), first term \(0<q_0<G\), and satisfies
\[
\boxed{6q_r=P\bigl(1+M(t_0+4r)\bigr).}
\tag{4}
\]
Choose q from this progression in the fixed interval
\[
\boxed{
\frac{\tau(\ell-1)+9\ell-37-5P}{14}
<q\le
\frac{\tau(\ell)-20\ell-43-5P}{15}.
}
\tag{5}
\]
Its length is exactly
\[
\Delta=\frac{27\cdot3^{\ell-1}+1}{420}
+\frac P{42}
-\frac{83\ell}{42}-\frac{47}{210}.
\tag{6}
\]
The left endpoint is positive and \(\Delta>G\) for every \(\ell\ge30\). Indeed
\(G\le(2/9)B^3\) by minimality of \(j\), whereas
\((27/420)3^{\ell-1}-2\ell-1>(2/9)B^3\)
holds at \(\ell=30\), and persists: the exponential positive term triples at each step, \(B^3\) grows by a factor below 3, and the negative linear part increases by only 2. So at least one even \(q_r\) lies in (5). Select the **least q greater than its lower endpoint**.

Useful consequences, elementary from (5) and \(P\le27B\), are
\[
q>\frac{3^{\ell-1}}{56},\qquad
q<\frac{3^\ell}{30},\qquad
q>9\ell,\qquad
3q-2>q+2.
\tag{7}
\]
The first follows from
\(\tau(\ell-1)+9\ell-37-5P>3^{\ell-1}/4\),
which holds at \(\ell=30\) and thereafter by the same exponential/polynomial comparison. The strict upper bound comes from (5).

## 2. Choose c using the **actual source digit-drain statistics**

Consider the source-defined successful **LE drain**
\[
\mathrm{drainB}(3q-2,\ q+2,\ 2).
\tag{8}
\]
Its success is guaranteed by the source budget
\(q+2\le\tau(3q-2)\) (the first counter is much greater than the logarithmic drain depth).

Let \(L\) be its digit length, \(D=L-2n_2\) its signed first-counter drop, and \(R=n_1+n_2\) its complete evaluator-call count. By \(2q+3<3^\ell\) and the source valuation-depth lemma,
\[
L\le\ell,\quad |D|\le\ell,\quad0\le R\le\ell,\quad
D+2R=L+2n_1\ge0.
\tag{9}
\]
These statistics depend **only on the drain budget q+2**: the existing source-certified LE shift theorem transports the drain outcome when the first counter is increased by any nonnegative integer \(c\), leaving \(D,R\) unchanged.

Now define the **positive** integer
\[
\boxed{c=9q+9D+8R+34+5P.}
\tag{10}
\]
Because \(q\) dominates \(\ell\), \(c>9q-9\ell>8q>0\).
The original LE high-level rule at \(D(4q+c,q)\) is
\[
\mathrm{highLevelNext}(D(4q+c,q))
=\mathrm{drainB}(3q+c-2,\ q+2,\ 2),
\]
and the exact source-certified digit formula yields
\[
(a',d')=(3q+c-2-D,\ 3q+8+2D+2R).
\tag{11}
\]
In particular \(q'=d'\) is even and
\[
p'=a'-d'=c-3D-2R-10
=9q+6D+6R+24+5P
=3q'+5P>0.
\]
The target is therefore also LE and has the **exact critical gap**
\[
\boxed{g'=p'-3q'=5P.}
\tag{12}
\]

Both input and target are inside the original newAffineCone. Indeed,
input LE has \(p=3q+c>q+4\), and target LE has
\(p'=3q'+5P>q'+4\); in each case the LE source budget
\(q+2\le\tau(p-2)\) follows immediately from
\(\tau(m)\ge m\) for positive \(m\), with the obvious sector parity and side inequalities.

The exact masses are
\[
S=5q+c=14q+9D+8R+34+5P,
\]
\[
S'=a'+d'=6q+c+D+2R+6
=15q+10D+10R+40+5P.
\]
From (9) and (5),
\[
S+3\ge14q-9\ell+37+5P>\tau(\ell-1),
\]
\[
S'+3\le15q+20\ell+43+5P\le\tau(\ell).
\]
Also \(S'-S=q+D+2R+6>0\). Hence source and target have **identical** S-depth \(\ell\) and **identical** window scale \(P,M,N\). This avoids *all* moving-cut ambiguity.

## 3. The input window is necessarily synchronizing

For the input LE, \(g=c\), hence the signed coordinates are
\[
X=2g-10=2c-10,\quad Y=6q.
\]
The integer combination governing the left full rectangle is
\[
A:=X-3Y
=2c-10-18q
=10P+(18D+16R+58).
\tag{13}
\]
By (9) and \(P>9B=306\ell+1098\), its correction satisfies
\[
-P<18D+16R+58<P.
\]
Thus \(\lfloor A/P\rfloor\in\{9,10\}\). Equation (4) says **Y is exactly divisible by P**, with \([\lfloor Y/P\rfloor]_M=1\). Since \(X=3Y+A\), the input word is
\[
\boxed{(x,y)=(12,1)\ \text{or}\ (13,1).}
\]
For both possibilities the exact four synchronization residues are:
\[
[x-3y]_M\in\{9,10\},\quad
[4x+3y]_M\in\{51,55\},\quad
[y]_N=1,\quad[x+y]_N\in\{13,14\}.
\]
Since \(n\ge8\), **all four residues satisfy the complete left-and-right rectangle criterion**. This conclusion holds for *every* allowed actual drain digit string, not just a sampled one.

Input \(g=c>8q\) yields \(h=g-5>8q-5\); for the gigantic \(q\) in (7), one has \(h^2>5q\), with a much stronger linear gap.

## 4. The target fails **both** synchronization and square-gap

From the exact target gap (12), its signed coordinate is
\[
X'=2g'-10=10P-10,
\]
so the target word's first digit coordinate is **exactly**
\[
\boxed{x'=\left[\left\lfloor X'/P\right\rfloor\right]_M=9.}
\]
The other global signed coordinate is
\[
Y'=6q'=18q+48+12D+12R
=3P(1+Mt)+\eta,\quad \eta:=48+12D+12R.
\]
Using (9) and \(P>306\ell+1098\), we have \(-P<\eta<P\).
Therefore
\[
\boxed{y'\in\{2,3\}.}
\]
In either case the left synchronization form is
\[
[x'-3y']_M\in\{3,0\},
\]
both in the **forbidden** residue set \(\{-2,-1,0,1,2,3\}\). Thus the target loses full-rectangle synchronization even though the source was fully synchronized.

The target LE old-ray distance is **exactly**
\[
h'=g'-5=5P-5.
\]
By (7), (9), \(q'=3q+8+2D+2R\ge3q-2\ell\), and
\(P\le27B\),
\[
q'>\frac{3^{\ell-1}}{28}
>25(27B)^2\ge (5P-5)^2
\qquad(\ell\ge30).
\tag{14}
\]
The middle strict inequality is verified at \(\ell=30\)
and persists, since the exponential left-hand side grows by 3
and the quadratic \(B^2\) by a factor below 3.
Hence
\[
\boxed{(h')^2<q',}
\]
as claimed. This violates even the factor-one square gap.

## 5. Reproduction and exact example

[verify_joint_sync_square_gap_nonclosure.js](verify_joint_sync_square_gap_nonclosure.js) independently executes the **original** source evalA/drainB recurrence in arbitrary-precision BigInt, determines \(D,R\) from a source-baseline drain, constructs \(c\) by (10), executes the exact original high-level successor, and checks all identities, source/target cone budgets, equal window cuts, synchronization pass/fail, and square-gap pass/fail for **every \(\ell=30,\ldots,100\)**. This finite scan supports the universally quantified proof but is not its substitute.

The first example, \(\ell=30\), is
\[
\boxed{
D(31864883370945,2451144867102)
\longrightarrow
D(29413738503831,7353434601354).}
\]
The baseline drain has \(D=10,R=10\), \(P=19683\). Source window \((13,1)\) synchronizes both rectangles, while the target window \((9,3)\) fails the left. The target satisfies \(h'=98410\) and \(q'=7353434601354>h'^2\), although the source has \(g=c=22060303902537>8q\) and \(h^2>5q\).

## Research significance and boundaries

This eliminates **two attractive but insufficient proposed universal inductive predicates simultaneously**. From even a heavily separated, fully synchronized **source-cone** state, one original source transition can land in an equally valid cone state where neither synchronization nor square-root terminal separation holds. The counterfamily is unbounded and keeps the S-window cut unchanged, so neither finite-size exceptions nor low-window cut shifts can explain it away.

**The authentic blank-tape orbit has not been shown to enter this synthetic family.** A proof that the actual root preserves synchronization and/or a square-gap property may still be possible, but it must involve a genuinely **reachability- or history-specific invariant** absent from the two pointwise tests. The result does not establish halting, nonhalting, an improved BB(6) bound, or the exact BB(6) value.
