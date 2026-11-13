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
M_d=\sum_{i=2}^d(t_i+1),
\]
such that, for every sufficiently large \(r\) in this class, the exact source reset-parent graph contains a chain
\[
z_d(n)\ \xrightarrow{\operatorname{ResetParent}}\ z_{d-1}(n)\
\xrightarrow{\operatorname{ResetParent}}\cdots
\xrightarrow{\operatorname{ResetParent}}\ z_0(n)
\]
of \(d\) odd-arm edges. For this density bound, take the first edge to have \((t_1,\sigma_1)=(4,9)\); the base divisibility \(3^8\mid Q\) makes its quotient odd and its next numerator \(G_1\) divisible by 3 on the entire progression.

Each fixed-depth family therefore has positive natural density \(3^{-M_d}\) in the progression parameter \(r\). The displayed cylinder is deliberately the seeded one: its final extra digit also makes \(3\mid G_d\), preparing the next edge; the \(d\)-edge chain itself needs one fewer digit. The finite five-point band lemma below gives \(t_i\le4\) for every later layer, so
\[
M_d=\sum_{i=2}^d(t_i+1)\le5(d-1).
\]
Thus the density is at least \(3^{-5(d-1)}\) at every fixed depth \(d\). The depth \(d\) is arbitrary, so there is no uniform finite inverse-depth bound over this fixed-depth U/Q family. This does **not** say that any of these candidate states is reachable from the authentic blank root, nor that a single fixed index has an infinite reverse path.

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

For the uniform density theorem, take the initial edge
\[
(t_1,\sigma_1)=(4,9),\qquad
R_1=\frac{(28/9)2^9}{3^5}=\frac{14336}{2187}\in(6,8),
\qquad
\gamma_1=\frac{1397}{4374}.
\]
Here \(e_1=Q/3^7\) is odd because \(3^8\mid Q\). The first parent has \(k_1=n-5\) and
\[
G_1=2^6e_1-16\cdot2^{n-5}-2(n-5)-5.
\]
Since \(3\mid e_1\), while \(k_1=n-5\) is both even and divisible by 3, we have \(2^{k_1}\equiv1\pmod3\) and \(3\mid G_1\) for every \(r\). Thus \(G_1/3\) is the initial scaled-cylinder Hensel function. The explicit seven-edge witness below uses a different first choice, \((7,14)\), to give a concrete deeper cylinder.

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

A stronger finite bound is available: for every \(\gamma>0\), some \(t\in\{0,1,2,3,4\}\) and integer \(\sigma\) satisfy
\[
6<\gamma\,2^\sigma/3^{t+1}<8.
\]
Put \(\alpha=\log_2 3\) and \(w=2-\alpha=\log_2(4/3)\). The elementary inequalities
\[
\frac32<\alpha<\frac85
\]
follow from \(8<9\) and \(3^5=243<256=2^8\). The five fractional parts of \(k\alpha\), \(k=1,\ldots,5\), are ordered as
\[
2\alpha-3<4\alpha-6<\alpha-1<3\alpha-4<5\alpha-7<1.
\]
Their consecutive circular gaps are
\[
2\alpha-3,\quad5-3\alpha,\quad2\alpha-3,\quad
2\alpha-3,\quad5-3\alpha.
\]
Both possible gap sizes are strictly smaller than \(w\): the first inequality is equivalent to \(3\alpha<5\), and the second to \(3<2\alpha\). Thus the five-point set has maximum gap \(<w\), so every translated open interval of length \(w\) contains one of its points. But the condition on \(\sigma\), after taking base-two logarithms, is exactly an interval of length
\[
3-\log_2 6=\log_2(4/3)=w
\]
for \(k=t+1\). Hence one of \(k=1,\ldots,5\) works, proving \(t\le4\).

For the density theorem, the initial layer is \((t_1,\sigma_1)=(4,9)\), and \(G_1/3\) is already an isometry on the full progression. At every later layer we may choose \(t_i\le4\). Since \(E_1=7\) and \(E_{i+1}=E_i+t_{i+1}+1\), the seeded-cylinder exponent is
\[
M_d=E_d-7=\sum_{i=2}^d(t_i+1)\le5(d-1).
\]
In particular, the construction gives the uniform explicit density lower bound \(3^{-5(d-1)}\) for every fixed depth \(d\), not merely an unspecified positive density.

## Hensel input and band-compatible iteration

The generic affine-exponential Hensel selector, including its scaled-cylinder form, is already derived in [Agent 44's AFFINE-EXP-HENSEL.md](../agent44-746-rank/AFFINE-EXP-HENSEL.md). Agent 10's [RayIndexHensel.lean](../agent10-cascade/RayIndexHensel.lean) also contains the source-coordinate nested-odd unique-digit criterion and recursive index selector for the signed-ray numerator. The argument here reuses that generic mechanism; it does not claim a new general Hensel lemma.

For this U/Q specialization, initially
\[
Q(n)=28\cdot2^n+B_0n+C_0,\qquad
B_0=-2-2^{3407}\equiv2\pmod3.
\]
The exact modular base check gives \(3^8\mid Q(887)\), and \(13122=6\cdot3^7=2\cdot3^8\). The common power-period identity, already kernel-proved as ThreeAdic.power_period in [ThreeAdicLifting.lean](../agent1-429-threeadic/ThreeAdicLifting.lean), gives the scaled-cylinder shift law. Thus \(Q/3^8\) is a 3-adic isometry in the progression parameter. For the density construction's first edge, \(t_1=4,\sigma_1=9\), so \(e_1=Q/3^7\) is odd and \(G_1=2^6e_1-16\cdot2^{n-5}-2(n-5)-5\). Since \(3\mid e_1\) and \(k_1=n-5\) is both even and divisible by 3, \(2^{k_1}\equiv1\pmod3\) and \(3\mid G_1\) on the whole progression. As \(E_1=7\), \(G_1/3=X_1/3^8\) is the initial scaled-cylinder isometry.

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

After the special first edge \((t_1,\sigma_1)=(4,9)\), the recursion is:
1. for each \(i\ge2\), choose \(t_i,\sigma_i\) with \(R_i=\gamma_{i-1}2^{\sigma_i}/3^{t_i+1}\in(6,8)\);
2. use the scaled Hensel selector on \(G_{i-1}/3\) to impose \(3^{t_i}\mid G_{i-1}/3\), equivalently \(3^{t_i+1}\mid G_{i-1}\);
3. form the odd parent \(z_i\) using the exact ResetParent formula;
4. select the unique next digit making \(3\mid G_i=2z_i+5\);
5. repeat.

The selected next digit need not give exact valuation \(v_3(G_{i-1})=t_i+1\). It may give a higher valuation. This is harmless: ResetParent requires only that the quotient \(e_i=G_{i-1}/3^{t_i+1}\) be odd, not 3-adically primitive. Requiring exact valuation would incorrectly discard the unique lift that continues the chain.

For the density construction, \(G_1\) is already divisible by 3 on the full progression, so \(G_1/3=X_1/3^8\) is the starting isometry. At every later stage, the scaled-cylinder selector lifts \(G_i/3\) to the requested precision, and the next unit digit selects \(3\mid G_{i+1}\).

After \(d\) parent edges and the final seed digit, the class has modulus
\[
3^{E_d-7}=3^{\,\sum_{i=2}^d(t_i+1)}.
\]
It contains infinitely many natural \(r\). Each of the finitely many band ratios is strictly inside \((6,8)\), so all corresponding integer band conditions hold once \(r\) is sufficiently large. This proves the stated arbitrary-finite-depth result and its positive density for each fixed depth.

## Explicit eight-edge specialization

The uniform-density initial edge also gives a dense concrete eight-edge branch. Choose
\[
\begin{aligned}
&(t_1,\sigma_1)=(4,9),\quad
(t_2,\sigma_2)=(0,6),\quad
(t_3,\sigma_3)=(0,7),\\
&(t_4,\sigma_4)=(1,9),\quad
(t_5,\sigma_5)=(1,11),\quad
(t_6,\sigma_6)=(1,12),\\
&(t_7,\sigma_7)=(0,12),\quad
(t_8,\sigma_8)=(1,14).
\end{aligned}
\]
The limiting band ratios are
\[
\begin{array}{c|c}
i&R_i\\\hline
1&14336/2187\approx6.5550983\\
2&44704/6561\approx6.8135955\\
3&147680/19683\approx7.5029213\\
4&1103168/177147\approx6.2274156\\
5&12626560/1594323\approx7.9197001\\
6&99988288/14348907\approx6.9683557\\
7&340741280/43046721\approx7.9156152\\
8&2696870336/387420489\approx6.9610937
\end{array}
\]
and all lie strictly inside \((6.2,7.93)\).

The exact Hensel digit choices give the eight-edge class
\[
\boxed{r\equiv1618\pmod{59049}.}
\]
The least representative has \(n=887+13122\cdot1618=21232283\). The successive unique lifts are:
\[
\begin{array}{c|c}
\text{condition}&\text{selected residue}\\\hline
3\mid G_2&r\equiv1\pmod3\\
3\mid G_3&r\equiv7\pmod9\\
9\mid G_3&r\equiv25\pmod{27}\\
3\mid G_4&r\equiv79\pmod{81}\\
9\mid G_4&r\equiv160\pmod{243}\\
3\mid G_5&r\equiv160\pmod{729}\\
9\mid G_5&r\equiv1618\pmod{2187}\\
3\mid G_6&r\equiv1618\pmod{6561}\\
3\mid G_7&r\equiv1618\pmod{19683}\\
9\mid G_7&r\equiv1618\pmod{59049}
\end{array}
\]
For the final lift, the three candidates \(r=1618,21301,40984\) give \(G_7\bmod9=(0,6,3)\), so the first is the unique digit making \(9\mid G_7\).

At the representative, modular evaluation gives
\[
\begin{aligned}
&Q\equiv224937324\pmod{3^{18}},\qquad
G_1\equiv18582\pmod{3^{11}},\qquad
G_2\equiv45384\pmod{3^{10}},\\
&G_3\equiv7605\pmod{3^9},\qquad
G_4\equiv1296\pmod{3^7},\qquad
G_5\equiv108\pmod{3^5},\\
&G_6\equiv6\pmod{3^3},\qquad
G_7\equiv0\pmod{3^2}.
\end{aligned}
\]
Thus
\[
v_3(Q)=9,\quad v_3(G_1)=1,\quad v_3(G_2)=1,\quad
v_3(G_3)=2,\quad v_3(G_4)=4,\quad v_3(G_5)=3,\quad
v_3(G_6)=1,\quad 9\mid G_7.
\]
A shift \(r\mapsto r+3^{10}a\) changes \(n\) by \(2a3^{18}\). The affine-exponential shift law therefore changes \(Q,G_1,\ldots,G_7\) by multiples of \(3^{18},3^{11},3^{10},3^9,3^7,3^5,3^3,3^2\), respectively. All displayed valuations and divisibilities consequently hold throughout the full class \(r\equiv1618\pmod{59049}\). Its density is \(1/59049\).

The eight band tests use the linear/constant coefficients \((B_i,C_i)\) of \(Q=X_0,X_1,\ldots,X_7\), whose bit lengths are
\[
(3408,3408),\ (3414,3414),\ (3416,3416),\ (3418,3418),\
(3421,3421),\ (3424,3424),\ (3427,3427),\ (3429,3429).
\]
Thus \(|B_i|,|C_i|<2^{3430}\) for every coefficient used in the eight band tests. Each factor \(2^{\sigma_i}/3^{t_i+1}\) is below \(2^{11}\). For \(n\ge7000\), \(n+1<2^{n/2}\), so the difference between each exact normalized band ratio and its limit is less than
\[
2^{11}\frac{2^{3430}(n+1)}{2^n}
<2^{3441-n/2}\le2^{-59}.
\]
Consequently every exact ratio lies in \((6.19,7.94)\), with margin greater than \(0.06\) from both endpoints 6 and 8. Also \(k_i=n+t_i-\sigma_i\ge n-13\), so \(0.06\cdot2^{k_i}>1\). The exact integer bands
\[
6\cdot2^{k_i}+1\le2^{t_i}e_i\le8\cdot2^{k_i}-1
\]
therefore hold for every \(n\ge7000\) in the class. In particular, the least representative itself gives a genuine eight-edge chain, and so does every nonnegative member of the class.

The exact modular residues, unique Hensel digits, coefficient bit lengths, and limiting ratios are reproduced by the accompanying NestedOddParentHenselCheck.mjs, using only modular BigInt exponentiation (it never constructs \(2^n\) as a full integer). Agent 44 independently checked an alternate eight-edge branch beginning with \((t_1,\sigma_1)=(7,14)\) modulo \(3^{28}\) in [NestedCascadeCheck.mjs](../agent44-746-rank/NestedCascadeCheck.mjs); that independent check is complementary to the denser \(t_1=4\) branch above.

## Scope and next formalization

- The result is about the exact ResetParent inverse relation and the fixed-depth \(j=3402\), \(n=887+13122r\) U/Q family. In FirstInverseComplete.lean, reset_parent_iff identifies this relation with the original source-C first-reset outcome.
- It rules out a strategy that seeks a uniform finite inverse-depth or fixed finite-cone cutoff across this family.
- It does not show that any member of the family lies on the authentic blank-root orbit. In particular, it is not a #746 nonhalting proof and says nothing by itself about the exact BB(6) value.
- The proof is currently a written arithmetic argument plus an exact modular specialization. The power-period ingredient is already kernel-proved as ThreeAdic.power_period in [ThreeAdicLifting.lean](../agent1-429-threeadic/ThreeAdicLifting.lean); reuse it rather than reproving the binomial lift. The next useful formalization is the affine-exponential 3-adic isometry using that lemma, followed by the recursive numerator update and one seven-level source ResetParent certificate. The generic Q-index selector is complementary and should be reused rather than reimplemented.
