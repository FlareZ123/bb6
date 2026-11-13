# Dense five-edge odd-parent branch from the t=4 seed

**Status: exact modular selector computations plus strict asymptotic band proof; not yet Lean-verified.** This is a separate, denser branch from the explicit t=7 cascade.

## 1. First edge without a Q-selector digit

Use
\[
n=887+13122r,\qquad j=3402,\qquad
Q(n)=28\cdot2^n-2n+15-2^{j+4}(2n+3).
\]
The established family identity gives \(Q=9(2z+5)\) and \(3^8\mid Q\) for every r. Choose
\[
t_1=4,\quad \sigma_1=9,\quad k_1=n-5,\quad
d_1=Q/3^7.
\]
Then \(d_1\) is odd, and
\[
\frac{2^{t_1}d_1}{2^{k_1}}
=\frac{2^9Q}{3^7 2^n}
\longrightarrow \frac{14336}{2187}\in(6,8).
\]
Thus the first odd parent exists for all sufficiently large r, with no 3-adic selector digit. Also n is odd, \(k_1=n-5\) is even, and \(k_1\equiv0\pmod3\). The next numerator
\[
G_1=2z_1+5=2^6d_1-16\cdot2^{k_1}-2k_1-5
\]
satisfies \(G_1\equiv0\pmod3\) for every r: the four terms are respectively \(0,-16,0,-5\pmod3\). Therefore \(X_1=3^7G_1\) is divisible by \(3^8\) on the entire r-family, and \(X_1/3^8=G_1/3\) is the initial scaled-cylinder 3-adic isometry.

## 2. Two further edges without additional digits

Choose
\[
(t_2,\sigma_2)=(0,6),\qquad (t_3,\sigma_3)=(0,7).
\]
The exact gamma recurrence gives
\[
\gamma_0=28/9,\quad
\gamma_1=1397/4374,\quad
\gamma_2=4615/26244,\quad
\gamma_3=17237/157464.
\]
The first three band limits are
\[
\frac{14336}{2187}\approx6.55510,\qquad
\frac{44704}{6561}\approx6.81360,\qquad
\frac{147680}{19683}\approx7.50292.
\]
All are strictly in (6,8). The first two divisibility conditions hold throughout the family. For the third edge, \(G_2\bmod3\) at r=0,1,2 is respectively \(2,0,1\), so the unique Hensel digit is
\[
r\equiv1\pmod3.
\]

## 3. Fourth and fifth edges

From \(\gamma_3=17237/157464\), choose
\[
(t_4,\sigma_4)=(1,9),\qquad
R_4=\frac{1103168}{177147}\approx6.22742.
\]
On \(r=1+3u\), exact modular evaluation of \(G_3\bmod9\), for u=0,...,8, gives
\[
7,5,3,1,8,6,4,2,0.
\]
The unique root is \(u\equiv8\pmod9\), hence
\[
r\equiv25\pmod{27}.
\]

Next, from \(\gamma_4=98645/2834352\), choose
\[
(t_5,\sigma_5)=(3,14),\qquad
R_5=\frac{1616199680}{229582512}\approx7.03973.
\]
On \(r=25+27u\), the unique root of \(G_4\bmod3^4\) is \(u\equiv59\pmod{81}\), obtained by evaluating \(X_4\bmod3^{15}\). Thus the five-edge cylinder is
\[
\boxed{r\equiv1618\pmod{2187}},
\]
of natural density \(1/2187\) in r. Its edge parameters are
\[
(t_i)=(4,0,0,1,3),\qquad
(\sigma_i)=(9,6,7,9,14).
\]

At the representative r=1618, n=21232283, modular evaluation gives
\[
v_3(Q)=9,\quad v_3(G_1)=1,\quad v_3(G_2)=1,\quad
v_3(G_3)=2,\quad v_3(G_4)=4.
\]
These are exactly the required divisibilities for the five selected exponents. Every quotient is odd; it need not be 3-coprime.

## 4. Uniform band justification and scope

For the affine-exponential recurrence \(X_i=A_i2^n+B_i n+C_i\), the bit lengths of \((B_i,C_i)\) through X5 are
\[
(3408,3408),(3414,3414),(3416,3416),(3418,3418),
(3421,3421),(3426,3426).
\]
The fifth band uses X4, whose coefficients have at most 3421 bits. Since \(\sigma_i\le14\), the band-ratio error is bounded by
\[
2^{14+3421}(n+1)/2^n.
\]
For n≥7000 this is below \(2^{-60}\), while the cylinder has n≥21232283. Hence all five strict limiting ratios give exact integer bands uniformly for sufficiently large members of the cylinder. Parent positivity follows from the lower band bound and large k.

This branch is substantially denser at depth five than the separate t1=7 branch \(r\equiv74803\pmod{3^{11}}\): its five-edge cylinder has density \(3^{-7}\), rather than \(3^{-11}\). It remains an intermediate inverse-cone result; it does not establish blank-root reachability or determine BB(6).


## 5. Sixth and seventh edges on a denser subcascade

The five-edge branch has
\[
\gamma_5=10904213/1836660096.
\]
Choose \(t_6=2,\sigma_6=15\), giving
\[
R_6=2791478528/387420489\approx7.20529.
\]
On \(r=1618+3^7a\), the unique root of \(G_5\bmod3^3\) is \(a\equiv1\pmod{27}\). This gives
\[
r\equiv3805\pmod{3^{10}}.
\]

The next gamma is
\[
\gamma_6=310449143/198359290368.
\]
Choose \(t_7=2,\sigma_7=17\), giving
\[
R_7=40691190071296/5355700839936\approx7.59773.
\]
On \(r=3805+3^{10}a\), the unique root of \(G_6\bmod3^3\) is
\(a\equiv23\pmod{27}\), hence the seven-edge cylinder
\[
\boxed{r\equiv1361932\pmod{3^{13}}},
\]
of density \(3^{-13}\). Its full parameter sequence is
\[
(t_i)=(4,0,0,1,3,2,2),\qquad
(\sigma_i)=(9,6,7,9,14,15,17).
\]

At the representative \(r=1361932\), \(n=17871272591\), modular evaluation gives
\[
(v_3(G_0),\ldots,v_3(G_6))=(7,1,1,2,6,3,6),
\]
which satisfies all seven divisibility requirements. The coefficient/constant bit lengths through X7 are
\[
(3408,3408),(3414,3414),(3416,3416),(3418,3418),
(3421,3421),(3426,3426),(3430,3430),(3434,3434).
\]
With \(\sigma_i\le17\), the error for the seventh band is bounded by
\(2^{3451}(n+1)/2^n\), far below \(2^{-60}\) on this cylinder.


## 6. Denser eight-edge path on the same t=4 seed

A different continuation after the fourth edge gives a denser eight-edge
cylinder. Take
\[
(t_i)=(4,0,0,1,1,1,0,1),\qquad
(\sigma_i)=(9,6,7,9,11,12,12,14).
\]
At r=1618, n=21232283, the exponents are
\(E_i=(2,7,8,9,11,13,15,16,18)\), and modular evaluation gives
\[
v_3(Q)=9,\qquad
(v_3(G_1),\ldots,v_3(G_7))=(1,1,2,4,3,1,5).
\]
The last selector is visible on the three lifts
\(r=1618+a3^9\), \(a=0,1,2\):
\[
G_7\bmod9=(0,6,3).
\]
Thus the unique final digit is a=0 and the eight-edge cylinder is
\[
\boxed{r\equiv1618\pmod{3^{10}}},
\]
of density \(3^{-10}=1/59049\).

The eight limiting band ratios are
\[
\frac{14336}{2187},\
\frac{44704}{6561},\
\frac{147680}{19683},\
\frac{1103168}{177147},\
\frac{12626560}{1594323},\
\frac{99988288}{14348907},\
\frac{340741280}{43046721},\
\frac{2696870336}{387420489},
\]
with decimal values approximately
\(6.5551,6.8136,7.5029,6.2274,7.9197,6.9684,7.9156,6.9611\).
All are strictly in (6,8).

The coefficient bit lengths through X7 are
\(3408,3414,3416,3418,3421,3424,3427,3429\) for both B_i and C_i.
The normalized factors \(2^{\sigma_i}/3^{E_i}\) are all below 1
(the maximum is \(512/2187\)); hence the band-ratio error is below
\(2^{-59}\) for n≥7000. The least n in this cylinder is 21232283,
so the integer bands hold uniformly.

This is the strongest t1=4 branch currently checked: eight edges on
density \(3^{-10}\), denser than the earlier t1=7 eight-edge cylinder
\(3^{-14}\). It is still an intermediate inverse-cone result, not a
blank-root reachability proof.
