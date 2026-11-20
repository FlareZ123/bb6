# E7 odd/even high-bounce fan is unbounded

**Status:** arithmetic and 2-adic parameter argument; not a reachability or nonhalting proof. This note explains why a fixed maximum bounce-depth search cannot close the exceptional E7/R branch.

## The residual target

The E7 reduction gives
\[
R(t)=(2861931660t+767469219,\;2092249530t+561067594),
\]
with odd left counter, even right counter, and (on the exceptional cylinder) \(t\equiv3\pmod4\). Its sum-plus-one is
\[
R_x+R_y+1
=4954181190t+1328536814
=2(2477090595t+664268407).
\]
Both coefficients in the final affine form are odd.

## Odd-a bounce parents

For any odd depth \(n\), the odd-a high-bounce source equations for a parent \((a,k)\) are
\[
R_x+R_y+1=2^n(2a+6)=2^{n+1}(a+3),
\]
\[
2k+a+7+3n=R_x+2R_y.
\]
If
\[
2^{n+1}\mid 2477090595t+664268407,
\]
put
\[
q=\frac{2477090595t+664268407}{2^{n+1}},
\qquad a=2q-3,
\]
and
\[
k=\frac{7046430720t+1889604407-a-7-3n}{2}.
\]
Then the first source equation holds exactly, a is odd, and for fixed n the inequalities a≥3 and 2k>a hold for all sufficiently large t in this residue class. The cost numerator is even because n and a are odd. Thus each such t admits a genuine odd-a bounce-parent branch at depth n.

Since 2477090595 is odd, for every fixed odd n there is a unique residue class of t modulo \(2^{n+1}\) satisfying the divisibility condition.

## The root32 family realizes every t residue

Write \(r=32+64j\). The exact root equation, after substituting \(u=1802+6720t\), is
\[
17300+22155(t+j)=5\cdot2^{E-17},
\]
proved by root32_tj_exact in D0EInverseArithmetic.lean. Here
\[
E=903171561+1761607680j.
\]
For any fixed modulus \(2^d\), choose j sufficiently large that \(E-17\ge d\). Then the right side is zero modulo \(2^d\), so
\[
22155(t+j)\equiv-17300\pmod{2^d}.
\]
Because 22155 is odd, this fixes \(t+j\) to one residue modulo \(2^d\). As j ranges over arbitrarily large integers in all residue classes modulo \(2^d\), the corresponding t values also range over every residue class modulo \(2^d\); and t tends to infinity.

Taking \(d=n+1\), the root32 candidate family therefore contains arbitrarily large t in the unique residue class that makes \(2^{n+1}\mid2477090595t+664268407\). Hence, for every fixed odd n, there are genuine root32 candidates for which the R(t) predecessor grammar admits a depth-n odd-a bounce branch.

## Consequence for the research strategy

There is no uniform finite odd-bounce-depth cutoff for the R(t) exceptional family. A search that only checks depths up to a fixed bound will leave actual root32 candidates with deeper admissible branches. The next proof must control the entire 2-adic bounce fan (or find a different invariant), rather than treating a finite list of bounce depths as exhaustive.

This does **not** say that any R(t) is blank-reachable: the existence of a source parent is only one branch in the backward reachability tree. The direct parent and all other bounce parents must still be handled.
