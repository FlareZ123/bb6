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

## Hensel input and band-compatible iteration

The generic affine-exponential Hensel selector, including its scaled-cylinder form, is already derived in [Agent 44's AFFINE-EXP-HENSEL.md](../agent44-746-rank/AFFINE-EXP-HENSEL.md). Agent 10's [RayIndexHensel.lean](../agent10-cascade/RayIndexHensel.lean) also contains the source-coordinate nested-odd unique-digit criterion and recursive index selector for the signed-ray numerator. The argument here reuses that generic mechanism; it does not claim a new general Hensel lemma.

For this U/Q specialization, initially
\[
Q(n)=28\cdot2^n+B_0n+C_0,\qquad
B_0=-2-2^{3407}\equiv2\pmod3.
\]
The exact modular base check gives \(3^8\mid Q(887)\), and \(13122=6\cdot3^7=2\cdot3^8\). The common power-period identity, already kernel-proved as ThreeAdic.power_period in [ThreeAdicLifting.lean](../agent1-429-threeadic/ThreeAdicLifting.lean), gives the scaled-cylinder shift law. Thus \(Q/3^8\) is a 3-adic isometry in the progression parameter.

At the first odd-parent stage, \(E_1=t_1+3\) and
\[
X_1=3^{E_1}G_1
=4\cdot2^{t_1}Q
-16\cdot2^{n+t_1-\sigma_1}3^{E_1}
-(2(n+t_1-\sigma_1)+5)3^{E_1}.
\]
For each later stage \(i\ge1\), put \(E_{i+1}=E_i+t_{i+1}+1\) and
\[
X_{i+1}
=4\cdot2^{t_{i+1}}X_i
-16\cdot2^{n+t_{i+1}-\sigma_{i+1}}3^{E_{i+1}}
-(2(n+t_{i+1}-\sigma_{i+1})+5)3^{E_{i+1}}.
\]
Each \(X_i\) has the form \(A_i2^n+B_i n+C_i\), with \(A_i,C_i\in\mathbb Z[1/2]\), and
\[
B_{i+1}=4\cdot2^{t_{i+1}}B_i-2\cdot3^{E_{i+1}}
\equiv4\cdot2^{t_{i+1}}B_i\not\equiv0\pmod3.
\]
The unit linear coefficient is therefore preserved at every layer. In the original progression, the shift law is
\[
X_i(n(r+a3^s))-X_i(n(r))
\equiv2B_i a\,3^{8+s}\pmod{3^{9+s}}.
\]
After restricting to the previously selected cylinder and dividing by its known power of 3, this is exactly the scaled-cylinder Hensel law in AFFINE-EXP-HENSEL.md. It gives one index cylinder for the required next divisibility and one of the three next-digit lifts for which the new target numerator is divisible by 3.

The recursion is consequently:
1. choose \(t_i,\sigma_i\) with \(R_i=\gamma_{i-1}2^{\sigma_i}/3^{t_i+1}\in(6,8)\);
2. use the scaled Hensel selector to impose \(3^{t_i+1}\mid G_{i-1}\);
3. form the odd parent \(z_i\) using the exact ResetParent formula;
4. select the unique next digit making \(3\mid G_i=2z_i+5\);
5. repeat.

The selected next digit need not give exact valuation \(v_3(G_{i-1})=t_i+1\). It may give a higher valuation. This is harmless: ResetParent requires only that the quotient \(e_i=G_{i-1}/3^{t_i+1}\) be odd, not 3-adically primitive. Requiring exact valuation would incorrectly discard the unique lift that continues the chain.

For the first stage, \(G_0=Q/9=3^6(Q/3^8)\). Choosing \(t_1\ge5\) asks for \(3^{t_1-5}\mid Q/3^8\), which the base isometry supplies on one residue class. The next digit then makes \(3\mid G_1\). At every later stage, the scaled-cylinder selector lifts the quotient \(G_i/3\) to the requested precision, and the next unit digit selects \(3\mid G_{i+1}\).

After \(d\) parent edges the final class has modulus
\[
3^{E_d-7}=3^{\,\sum_{i=1}^d t_i+d-5}.
\]
It contains infinitely many natural \(r\). Each of the finitely many band ratios is strictly inside \((6,8)\), so all corresponding integer band conditions hold once \(r\) is sufficiently large. This proves the stated arbitrary-finite-depth result and its positive density for each fixed depth.

## Explicit five-edge specialization

The following choices give five successive bands:
\[
(t_1,\sigma_1)=(7,14),\quad
(t_2,\sigma_2)=(1,9),\quad
(t_3,\sigma_3)=(0,9),\quad
(t_4,\sigma_4)=(2,13),\quad
(t_5,\sigma_5)=(1,13).
\]
Their limiting band ratios are
\[
\begin{array}{c|c}
i&R_i\\\hline
1&458752/59049\approx7.7690054\\
2&3560896/531441\approx6.7004540\\
3&11481056/1594323\approx7.2012108\\
4&326640896/43046721\approx7.5880552\\
5&2471264192/387420489\approx6.3787648
\end{array}
\]
and are all strictly between 6 and 8.

Exact modular evaluation gives the compatible class
\[
\boxed{r\equiv74803\pmod{177147}.}
\]
Its least nonnegative representative has \(n=887+13122\cdot74803=981565853\). On this class the successive target numerators satisfy
\[
v_3(Q)=10,\qquad
v_3(G_1)=2,\qquad
v_3(G_2)=1,\qquad
v_3(G_3)\ge4,\qquad
v_3(G_4)=2,\qquad
3\mid G_5.
\]
The inequality \(v_3(G_3)\ge4\), rather than exact valuation 3, is intentional: \(t_4=2\) only needs \(27\mid G_3\). The extra factor of 3 is allowed because the odd ResetParent arm requires only an odd quotient. The five-edge class has density \(1/177147\) in \(r\), and is a subcylinder of the four-edge prefix \(r\equiv15754\pmod{19683}\).

The five limiting band ratios all lie in \((6.2,7.9)\), and each factor \(2^{\sigma_i}/3^{t_i+1}\) is below \(2^{10}\). The coefficient recurrence gives the following bit lengths for the linear and constant coefficients \((B_i,C_i)\) of \(Q=X_0,X_1,\ldots,X_4\):
\[
(3408,3408),\ (3417,3417),\ (3420,3420),\ (3422,3422),\ (3426,3426).
\]
Thus \(|B_i|,|C_i|<2^{3430}\) for every coefficient used in the five band tests. For \(n\ge7000\), \(n+1<2^{n/2}\), so the difference between each exact normalized band ratio and its limit is less than
\[
2^{10}\frac{2^{3430}(n+1)}{2^n}
<2^{3440-n/2}\le2^{-60}.
\]
Consequently every exact ratio remains strictly between 6 and 8 with margin greater than \(0.1\). Also \(k_i=n+t_i-\sigma_i\ge n-14\), so \(0.1\cdot2^{k_i}>1\). The integer bands \(6\cdot2^{k_i}+1\le2^{t_i}e_i\le8\cdot2^{k_i}-1\) therefore hold for every \(n\ge7000\) in the class. In particular, the least representative \(r=74803\) itself gives a genuine five-edge chain, and so does every nonnegative member of the class.

The exact modular residues and coefficient bit lengths are reproduced by the accompanying NestedOddParentHenselCheck.mjs, using only modular BigInt exponentiation (it never constructs \(2^n\) as a full integer). The calculation checks the finite specialization; the band-compatible induction above is the arbitrary-depth mathematical argument.

## Scope and next formalization

- The result is about the exact ResetParent inverse relation and the fixed-depth \(j=3402\), \(n=887+13122r\) U/Q family. In FirstInverseComplete.lean, reset_parent_iff identifies this relation with the original source-C first-reset outcome.
- It rules out a strategy that seeks a uniform finite inverse-depth or fixed finite-cone cutoff across this family.
- It does not show that any member of the family lies on the authentic blank-root orbit. In particular, it is not a #746 nonhalting proof and says nothing by itself about the exact BB(6) value.
- The proof is currently a written arithmetic argument plus an exact modular specialization. The power-period ingredient is already kernel-proved as ThreeAdic.power_period in [ThreeAdicLifting.lean](../agent1-429-threeadic/ThreeAdicLifting.lean); reuse it rather than reproving the binomial lift. The next useful formalization is the affine-exponential 3-adic isometry using that lemma, followed by the recursive numerator update and one four-level source ResetParent certificate. The generic Q-index selector is complementary and should be reused rather than reimplemented.
