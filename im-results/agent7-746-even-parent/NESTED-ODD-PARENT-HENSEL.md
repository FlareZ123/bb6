# Nested odd-parent Hensel cascade on the fixed-depth U ray

**Status:** a mathematical derivation for the exact odd-arm relation in the checked-in #746 reset grammar. It is not yet Lean-formalized. The finite residue example below is exact modular computation. This is an inverse-graph depth result, **not** a blank-root reachability or nonhalting theorem.

## The result

Fix
\[
j=3402,\qquad n=887+13122r,\qquad
Q(n)=28\cdot2^n-2n+15-2^{3406}(2n+3),
\]
and the first-tier U/Q candidate
\[
z_0(n)=\frac{Q(n)/9-5}{2}.
\]
The existing U/Q coordinate construction supplies this first-tier state on the relevant large-\(n\) branch. Since \(Q(n)\) is divisible by \(3^8\) throughout the progression, \(z_0(n)\) is integral.

For every finite depth \(d\ge1\), there are fixed nonnegative odd-parent exponents \(t_1,\ldots,t_d\), fixed integer offsets \(\sigma_1,\ldots,\sigma_d\), and a residue class
\[
r\equiv r_d\pmod{3^{M_d}},\qquad
M_d=\sum_{i=1}^d t_i+d-5,
\]
such that, for every sufficiently large \(r\) in this class, the exact source reset-parent graph contains a chain
\[
z_d(n)\ \xrightarrow{\operatorname{ResetParent}}\ z_{d-1}(n)\
\xrightarrow{\operatorname{ResetParent}}\cdots
\xrightarrow{\operatorname{ResetParent}}\ z_0(n)
\]
of \(d\) odd-arm edges.

Each fixed-depth family therefore has positive natural density \(3^{-M_d}\) in the progression parameter \(r\). The depth \(d\) is arbitrary, so there is no uniform finite inverse-depth bound over this fixed-depth U/Q family. This does **not** say that any of these candidate states is reachable from the authentic blank root, nor that a single fixed index has an infinite reverse path.

## Exact odd-arm rule

Write \(G=2v+5\) for a target reset height \(v\). If
\[
G=3^{t+1}e,\qquad e\ \text{odd},
\]
and for some \(k\ge0\)
\[
6\cdot2^k+1\le 2^t e\le8\cdot2^k-1,
\]
then the odd constructor of CascadeResetInverse.ResetParent in [FirstInverseComplete.lean](../agent10-cascade/FirstInverseComplete.lean) gives the predecessor
\[
p=2^{t+1}e-8\cdot2^k-k-5,\qquad
\operatorname{ResetParent}(p,v).
\]
There is no requirement that \(3\nmid e\). In particular, if \(G\) is divisible by more than \(3^{t+1}\), the same exponent \(t\) remains valid: the quotient \(e\) is still odd because \(G\) and \(3^{t+1}\) are odd.

Set \(k=n+t-\sigma\). If
\[
\frac{G(n)}{2^n}\longrightarrow\gamma>0
\]
and
\[
R=\frac{\gamma\,2^\sigma}{3^{t+1}}\in(6,8),
\]
then
\[
\frac{2^t e}{2^k}
=\frac{G(n)}{2^n}\frac{2^\sigma}{3^{t+1}}
\longrightarrow R.
\]
Since \(k\to\infty\), the exact integer band inequalities hold for all sufficiently large \(n\) in any fixed residue class under consideration. The resulting predecessor is positive for sufficiently large \(n\).

## Leading-coefficient recurrence

Let \(z_0\) be as above and put \(G_0=2z_0+5=Q/9\). Then
\[
\gamma_0=\lim_{r\to\infty}\frac{G_0(n(r))}{2^{n(r)}}=\frac{28}{9}.
\]

Suppose at stage \(i\) we have a target \(z_{i-1}\), with
\[
G_{i-1}=2z_{i-1}+5,\qquad
\frac{G_{i-1}(n(r))}{2^{n(r)}}\longrightarrow\gamma_{i-1}>0.
\]
Choose \(t_i,\sigma_i\) so that
\[
R_i=\frac{\gamma_{i-1}2^{\sigma_i}}{3^{t_i+1}}\in(6,8).
\]
On the appropriate 3-adic residue class, let
\[
e_i=\frac{G_{i-1}}{3^{t_i+1}},\qquad
k_i=n+t_i-\sigma_i,
\]
and define
\[
z_i=2^{t_i+1}e_i-8\cdot2^{k_i}-k_i-5.
\]
Then \(\operatorname{ResetParent}(z_i,z_{i-1})\) for all sufficiently large indices in that class, and
\[
G_i=2z_i+5
=2^{t_i+2}e_i-16\cdot2^{k_i}-2k_i-5.
\]
Consequently
\[
\boxed{\displaystyle
\gamma_i=4\cdot2^{t_i-\sigma_i}(R_i-4)>0.}
\]
Thus every stage again has a positive finite leading ratio.

For any fixed \(\gamma>0\), there are infinitely many pairs \((t,\sigma)\), \(t\ge0\), with
\[
6<\gamma\,2^\sigma/3^{t+1}<8.
\]
Indeed, taking base-two logarithms reduces this to the density modulo one of \((t+1)\log_2 3-\log_2\gamma\); the target interval has width \(\log_2(8/6)=\log_2(4/3)>0\). Since \(\log_2 3\) is irrational, the rotation is dense. This supplies a band choice at every finite stage.

## The 3-adic lifting mechanism

The key point is that the numerator remains affine-exponential with a unit linear coefficient.

Initially
\[
Q(n)=28\cdot2^n+B_0n+C_0,\qquad
B_0=-2-2^{3407}\equiv2\pmod3.
\]
For the first edge, take \(X_0=Q\), \(G_0=Q/9\), and
\(E_1=t_1+3\), so that \(X_1=3^{E_1}G_1\). For every later stage
\(i\ge1\), write
\[
X_i(n)=3^{E_i}G_i(n)=A_i2^n+B_i n+C_i,
\]
where \(A_i,C_i\in\mathbb Z[1/2]\), \(B_i\in\mathbb Z\), and
\(3\nmid B_i\). At later stages
\[
E_{i+1}=E_i+t_{i+1}+1.
\]
The parent formula gives the exact recurrence
\[
X_{i+1}
=4\cdot2^{t_{i+1}}X_i
-16\cdot2^{n+t_{i+1}-\sigma_{i+1}}3^{E_{i+1}}
-(2(n+t_{i+1}-\sigma_{i+1})+5)3^{E_{i+1}},
\]
valid for \(i\ge1\), with the same displayed formula for \(X_1\) when
\(i=0\) and \(X_0=Q\).
In particular,
\[
B_{i+1}=4\cdot2^{t_{i+1}}B_i-2\cdot3^{E_{i+1}}
\equiv4\cdot2^{t_{i+1}}B_i\not\equiv0\pmod3.
\]
Thus the unit condition persists at every level.

For any \(X(n)=A2^n+Bn+C\) of this form and any \(a,s\ge0\),
\[
\begin{aligned}
&X(n(r+a3^s))-X(n(r))\\
&\quad=A2^{n(r)}(2^{2a3^{8+s}}-1)+2B\,a\,3^{8+s}\\
&\quad\equiv2B\,a\,3^{8+s}\pmod{3^{9+s}},
\end{aligned}
\]
using \(3^{9+s}\mid 2^{2\cdot3^{8+s}}-1\). The first term is divisible by \(3^{9+s}\), while \(3\nmid2B\). Hence this is a scaled 3-adic isometry.

If \(3^{E_i}\mid X_i\) on a residue class modulo \(3^{E_i-8}\), then \(G_i=X_i/3^{E_i}\) is integer-valued there. On the three next-digit lifts
\[
r,\quad r+3^{E_i-8},\quad r+2\cdot3^{E_i-8},
\]
the residues of \(G_i\pmod3\) differ by the unit step \(2B_i\). Exactly one lift therefore has \(3\mid G_i\). Choose that lift. This is the crucial recursive choice.

On the selected class modulo \(3^{E_i-7}\), \(G_i\) is divisible by 3. The quotient \(G_i/3\) is again a 3-adic isometry in the local parameter
\[
q=(r-r_i)/3^{E_i-7}.
\]
For any chosen \(t_{i+1}\), there is a unique further residue class modulo \(3^{t_{i+1}}\) in \(q\) on which \(3^{t_{i+1}}\mid G_i/3\). Equivalently,
\[
3^{t_{i+1}+1}\mid G_i.
\]
This gives the next odd quotient \(e_{i+1}\) and parent. The cumulative exponent increases to \(E_{i+1}=E_i+t_{i+1}+1\); choosing one of its three next-digit lifts makes \(3\mid G_{i+1}\), and the construction repeats.

Importantly, the chosen next-digit lift need **not** give exact valuation \(v_3(G_i)=t_{i+1}+1\). It may give a higher valuation. This is harmless: the ResetParent relation only requires the quotient \(e_{i+1}\) to be odd, not 3-adically primitive. Requiring exact valuation would incorrectly discard the unique lift that continues the chain.

The first stage starts from \(Q/3^8\), which is integer-valued for every \(r\). Since \(Q(887)\equiv0\pmod{3^8}\) and \(13122=2\cdot3^8\), the exponential difference and linear term preserve this divisibility throughout the progression. Choosing \(t_1\ge5\) asks for
\[
3^{t_1-5}\mid Q/3^8,
\]
which the same isometry supplies on one residue class. One next-digit lift then makes \(3\mid G_1\).

After \(d\) parent edges the final class has modulus
\[
3^{E_d-7}=3^{\,\sum_{i=1}^d t_i+d-5}.
\]
It contains infinitely many natural \(r\). Each of the finitely many band ratios is strictly inside \((6,8)\), so all corresponding integer band conditions hold once \(r\) is sufficiently large. This proves the stated arbitrary-finite-depth result and its positive density for each fixed depth.

## Explicit four-edge specialization

The following choices give four successive bands:
\[
(t_1,\sigma_1)=(7,14),\quad
(t_2,\sigma_2)=(1,9),\quad
(t_3,\sigma_3)=(0,9),\quad
(t_4,\sigma_4)=(2,13).
\]
Their limiting band ratios are
\[
\begin{array}{c|c}
i&R_i\\\hline
1&458752/59049\approx7.7690054\\
2&3560896/531441\approx6.7004540\\
3&11481056/1594323\approx7.2012108\\
4&326640896/43046721\approx7.5880552
\end{array}
\]
and are all strictly between 6 and 8.

Exact modular evaluation gives the compatible class
\[
\boxed{r\equiv15754\pmod{19683}.}
\]
On this class the successive target numerators satisfy
\[
v_3(Q)=10,\qquad
v_3(G_1)=2,\qquad
v_3(G_2)=1,\qquad
v_3(G_3)\ge4,\qquad
3\mid G_4.
\]
The inequality \(v_3(G_3)\ge4\), rather than exact valuation 3, is intentional: \(t_4=2\) only needs \(27\mid G_3\). The extra factor of 3 is precisely what allows the selected next-digit lift to make \(3\mid G_4\). The class has density \(1/19683\) in \(r\). The four dyadic bands hold for every sufficiently large member of the class.

The exact modular residues can be reproduced with the accompanying NestedOddParentHenselCheck.mjs. This finite calculation checks the displayed specialization; the induction above is the unbounded mathematical argument.

## Scope and next formalization

- The result is about the exact ResetParent inverse relation and the fixed-depth \(j=3402\), \(n=887+13122r\) U/Q family. In FirstInverseComplete.lean, reset_parent_iff identifies this relation with the original source-C first-reset outcome.
- It rules out a strategy that seeks a uniform finite inverse-depth or fixed finite-cone cutoff across this family.
- It does not show that any member of the family lies on the authentic blank-root orbit. In particular, it is not a #746 nonhalting proof and says nothing by itself about the exact BB(6) value.
- The proof is currently a written arithmetic argument plus an exact modular specialization. The power-period ingredient is already kernel-proved as ThreeAdic.power_period in [ThreeAdicLifting.lean](../agent1-429-threeadic/ThreeAdicLifting.lean); reuse it rather than reproving the binomial lift. The next useful formalization is the affine-exponential 3-adic isometry using that lemma, followed by the recursive numerator update and one four-level source ResetParent certificate. The generic Q-index selector is complementary and should be reused rather than reimplemented.
