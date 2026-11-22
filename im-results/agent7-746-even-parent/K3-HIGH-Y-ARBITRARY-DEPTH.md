# Arbitrarily deep odd-parent ancestry in a K3 high-Y residue family

**Status:** new intermediate theorem, paper-level proof; not Lean-certified. This is a result about the exact inverse-reset graph, not about blank-root reachability. It instantiates the generic nested-odd/Hensel mechanism from [NESTED-ODD-PARENT-HENSEL.md](NESTED-ODD-PARENT-HENSEL.md) in the K3 high-(Y) family that the third-lift argument had treated as parentless.

## Theorem

Let
[
mathcal W=[803/512,1659/1024],qquad
x=(2K+7)/2^a,qquad p=2^K,
]
and define
[
T=80p+2K+13-2(2K+7)2^{K+4-a},quad
X=T/3,quad E=(X-5)/2.
]
Set
[
h=2(X/3)-4p-K-4,quad Y=2h+5,quad
G=2(Y/3)-2p-K-3,quad Z_0=2G+5.
]

For every prescribed finite depth (d), there is a threshold (A_d) such that for every odd (a\ge A_d), the following construction gives a (K\in\mathcal W) and a chain of (d+2) genuine odd-arm ResetParent edges starting at (E).

For each such (a), take the unique high-X residue (K_*\pmod{162}) satisfying
[
K_*\equiv48-3a\pmod{54},\qquad h(K_*)\equiv2\pmod9.
]
Among (K_*,K_*+162,K_*+324\pmod{486}), exactly one class (K_0(a)\pmod{486}) has (Z_0(K_0)\equiv0\pmod9). The Hensel construction selects a further residue class modulo a finite (L_d), still reducing to (K_0(a)\pmod{486}); for sufficiently large (a), the K-window contains a representative of that class with (x) near (x_0=79/50).

The theorem does **not** assert that one fixed (E) has an infinite reverse path, or that any of these states is reachable from the authentic blank root (2). It asserts that no uniform finite inverse-depth cutoff can exclude this residue family as (a) varies.

## 1. Exact seed residue and the first two parents

A concrete representative of the general selected class is given by the congruences
[
a\equiv15\pmod{162},qquad K\equiv219\pmod{486}
]
give, by direct modular calculation,
[
2^K\equiv170\pmod{243},qquad
2^{K+4-a}\equiv25\pmod{243},qquad
2K+7\equiv202\pmod{243}.
]
Consequently
[
T\equiv63\pmod{243},quad X\equiv21\pmod{81}.
]
Continuing the exact divisions gives
[
h\equiv2\pmod{27},quad Y\equiv9\pmod{27},quad
g:=Y/3\equiv3\pmod9,quad
G\equiv2\pmod9,quad Z_0\equiv0\pmod9.
]
In particular (v_3(X)=1), (v_3(Y)=2), and (9\mid Z_0). For this representative, the selected class is one of the non-high (Y\bmod27\in\{9,18\}) third-lift classes, not the (Y\equiv0\pmod{27}) survivor. In general, every high-X class (K_*\pmod{162}) has (X\equiv3\pmod9), (h\equiv2\pmod9), and (9\mid Y); the same two (t=0) parent constructions and uniform source-band bounds below therefore apply to all three of its third lifts.

The first edge (h\to E) in inverse-parent notation is (t=0,k=K-1), with odd source parameter (d=X/3). Its exact normalized height is
[
rac dp=\frac{80-32x+(2K+13)/p}{9},
]
which lies strictly between (3) and (4) on (mathcal W). Thus (d) lies in the odd source band at scale (K-1), and (h) is a genuine odd ResetParent of (E).

The second edge (G\to h) also has (t=0), with odd source parameter (g=Y/3). Here
[
rac gp=\frac{248-128x+(25-10K)/p}{27},
]
and for (K\ge266), (x\in\mathcal W), this is strictly between (3/2) and (7/4). Hence (g) lies in the odd source band at scale (K-2), and (G) is a genuine odd ResetParent of (h).

The target (G) therefore has numerator (Z_0=2G+5), divisible by (9), which is the input to the nested construction.
## 1.1. The 9-divisible third lift exists for every odd a

The second-lift table gives, for every odd (a), a unique high-X class (K_*\pmod{162}) with (h\equiv2\pmod9), inside the phase (K\equiv48-3a\pmod{54}). Thus (Y=2h+5\equiv0\pmod9) on this class.

For (Delta=162), (2^\Delta\equiv1\pmod{243}). Since (e=K+4-a) is even, direct subtraction in (T) gives
[
T(K+162)-T(K)
\equiv(4-8\cdot2^e)3^4
\equiv162\pmod{243}.
]
Dividing successively through (X,h,Y,g=Y/3,G,Z_0) gives
[
Y(K+162)\equiv Y(K)+18\pmod{27},qquad
Z_0(K+162)\equiv Z_0(K)+6\pmod9.
	ag{1a}
]
The three lifts (K_*,K_*+162,K_*+324\pmod{486}) therefore cycle (Y\bmod27) through (0,9,18), and (Z_0\bmod9) through (0,3,6). Exactly one of the three lifts has (9\mid Z_0), for every odd (a).

It is also possible to identify whether this selected class is the high-Y lift or one of the two non-high lifts. On the high-Y lift (Y\equiv0\pmod{27}), so (g=Y/3\equiv0\pmod9). Since (K\equiv48-3a\pmod{54}), (K\equiv3(1-a)\pmod9), while (2^K\equiv8\pmod9). Hence
[
Z_0\equiv3-2K\equiv3(2a-1)\pmod9
quad\text{on the high-Y lift.}
	ag{1b}
]
If (a\equiv0) or (1\pmod3), the high-Y lift has (Z_0\not\equiv0\pmod9), so the unique (9\mid Z_0) class is one of the two non-high (Y\bmod27\in\{9,18\}) lifts. If (a\equiv2\pmod3), the high-Y lift itself is the selected class. Thus the lower-t Hensel branch occurs among the two classes previously counted as excluded for two-thirds of odd (a) residue classes. The all-81-odd-residue modular audit is reproducible in [k3_third_lift_selector.mjs](k3_third_lift_selector.mjs); it checks the unique high-X selector, both three-cycles, the high-Y formula, and the 27/27/27 split.



## 2. Base 3-adic isometry

The exact shift law derived in [K3-LOWER-T-PARENT-STRUCTURE.md](K3-LOWER-T-PARENT-STRUCTURE.md) is
[
Z_0(K+486\cdot3^s)
\equiv Z_0(K)+2\cdot3^{s+2}
\pmod{3^{s+3}}
qquad(s\ge0).
	ag{1}
]
For any fixed odd (a), let (K_0(a)\pmod{486}) be the unique third-lift class from Section 1.1 with (9\mid Z_0(K_0)). The shift law preserves this divisibility throughout the progression. Thus, writing (K=K_0(a)+486m),
[
Phi_0(m)=Z_0(K_0+486m)/9
]
satisfies
[
Phi_0(m+3^s)-Phi_0(m)
\equiv2\cdot3^s\pmod{3^{s+1}}.
]
This is a 3-adic isometry with unit slope (c_0=2). In particular, for every (r\ge1), there is a unique residue class (m\bmod3^r) on which (3^r\midPhi_0(m)).

The leading coefficient of the seed numerator is
[
gamma_0(x_0)=\lim_{K\to\infty,,x\to x_0}rac{Z_0(K)}{2^K}
=\frac{884-512x_0}{27}>0.
]
Fix, for example, (x_0=79/50\inoperatorname{int}(\mathcal W)). Then
[
gamma_0=1876/675.
]

## 3. Band-compatible recursive step

A slightly stronger central-band form follows from the same five points. Put (	heta=\log_2(3/2)). The fractional parts of (0,\theta,2\theta,3\theta,4\theta), in increasing order, are
[
0, 2\theta-1, 4\theta-2, \theta, 3\theta-1.
]
The circular gaps are (2\theta-1) and (2-3\theta), with maximum (2-3\theta). Moreover,
[
2^{2-3\theta}=\frac{32}{27}<\frac{31}{25},
]
so the maximum gap is strictly smaller than (\log_2(31/25)). Taking base-2 logarithms, the ratio condition asks that a translate of an interval of length (\log_2(31/25)) contain one of the five points ({(t'+1)\theta}); these are a rotation of the five displayed points. The max-gap bound therefore proves that, for every (gamma>0), there are (t'\in\{0,1,2,3,4\}) and (\sigma\in\mathbb Z) such that
[
\frac{\gamma2^\sigma}{3^{t'+1}}\in\left(\frac{25}{4},\frac{31}{4}\right).
]
Applying this to (gamma/3) gives the shifted form used below:
[
t\in\{1,2,3,4,5\},\qquad
R:=\frac{\gamma2^\sigma}{3^{t+1}}\in\left(\frac{25}{4},\frac{31}{4}\right).
\tag{2}
]
This leaves a uniform (1/4) margin from the odd source-band endpoints 6 and 8.

At stage (i), suppose the target is (u_i(K)), its numerator is (Z_i(K)=2u_i(K)+5), and on a progression (K=K_i+L_i m) the function
[
Phi_i(m)=Z_i(K_i+L_i m)/3^{\nu_i}
]
is a 3-adic isometry with unit slope (c_i). Initially ((L_0,\nu_0,c_0)=(486,2,2)); after the first constructed edge, (
u_i=1).

Let
[
\gamma_i=\limrac{Z_i(K)}{2^K}>0.
]
Choose (t_i\in\{1,\ldots,5\}) and (sigma_i\in\mathbb Z) by (2), so
[
R_i=\frac{\gamma_i2^{\sigma_i}}{3^{t_i+1}}\in\left(\frac{25}{4},\frac{31}{4}\right).
]
Put (r_i=t_i+1-\nu_i\ge0). By the isometry, there is a unique (m\bmod3^{r_i}) for which
[
3^{r_i}\mid\Phi_i(m),
]
equivalently (3^{t_i+1}\mid Z_i(K)). Thus
[
d_i=Z_i(K)/3^{t_i+1}
]
is an odd integer. Set
[
k_i=K+t_i-\sigma_i,qquad
u_{i+1}=2^{t_i+1}d_i-8\cdot2^{k_i}-k_i-5.
]
The normalized source parameter satisfies
[
rac{2^{t_i}d_i}{2^{k_i}}
=rac{Z_i(K)}{2^K}\frac{2^{\sigma_i}}{3^{t_i+1}}
\longrightarrow R_i\in(25/4,31/4).
]
For sufficiently large (K) in a sufficiently small fixed neighborhood of (x_0), the exact integer source-band inequalities
[
6\cdot2^{k_i}+1\le2^{t_i}d_i\le8\cdot2^{k_i}-1
]
therefore hold. This proves
[
operatorname{ResetParent}(u_{i+1},u_i).
]
The next numerator is
[
Z_{i+1}=2u_{i+1}+5
=2^{t_i+2}d_i-16\cdot2^{k_i}-2k_i-5.
	ag{3}
]
Its leading coefficient is
[
oxed{\gamma_{i+1}
=4\cdot2^{t_i-\sigma_i}(R_i-4)>0.}
	ag{4}
]
Thus the band-selection step can be repeated indefinitely at the level of leading coefficients.

## 4. Hensel digit and preservation of the isometry

After imposing (3^{t_i+1}\mid Z_i), vary (m) by the next base-3 digit:
[
m\longmapsto m+e,3^{r_i},qquad e\in\{0,1,2\}.
]
The isometry of (Phi_i) gives
[
\DeltaPhi_i\equiv c_i3^{r_i}\pmod{3^{r_i+1}},
qquad
\Delta d_i\equiv c_i\pmod3.
]
The scale (k_i=K+t_i-\sigma_i) changes by a multiple of (486), so (2^{k_i}\pmod3) is unchanged; the linear term (-2k_i) is also unchanged modulo 3. Equation (3) therefore gives
[
\Delta Z_{i+1}\equiv2^{t_i+2}c_i\pmod3,
]
a unit. The three choices (e=0,1,2) give all residues modulo 3, so exactly one makes (3\mid Z_{i+1}).

Restrict to that lift. The new progression modulus is
[
L_{i+1}=L_i3^{r_i+1},
]
and (
u_{i+1}=1). For a further shift by (L_{i+1}3^s), the old isometry gives
[
\Delta d_i\equiv c_i3^{s+1}\pmod{3^{s+2}}.
]
The power-of-two and linear terms in (3) are unchanged modulo (3^{s+2}), so
[
\Delta(Z_{i+1}/3)
\equiv2^{t_i+2}c_i3^s\pmod{3^{s+1}}.
]
Hence (Z_{i+1}/3) is again a 3-adic isometry, with unit slope
[
c_{i+1}\equiv2^{t_i+2}c_i\not\equiv0\pmod3.
]
This closes the induction. Notice that no exact-valuation assumption is used: if (Z_{i+1}) is divisible by a higher power of 3, the quotient remains odd and the same construction works.

## 5. Fitting the Hensel cylinder inside the dyadic window

For a fixed depth (d), the choices (t_i\in\{1,\ldots,5\}) and (sigma_i) are fixed by the positive leading coefficients (4). The progression modulus after (d) steps is finite:
[
L_d=486\cdot3^{M_d}
]
for a finite integer (M_d). The (K)-length of (mathcal W) is
[
\frac{53}{2048}2^a.
]
More strongly, any fixed open subinterval around (x_0=79/50) has (K)-length proportional to (2^a). The base class (K_0(a)\pmod{486}) exists for every odd (a), and this length tends to infinity through odd (a). Therefore, for all sufficiently large odd (a), the required Hensel residue cylinder modulo (L_d) has a representative with (x) in that open subinterval. All source-band limits used above are then uniform for the finitely many stages (i\le d).

This supplies the required (K\inmathcal W) and completes the finite-depth construction.

For reference, with (x_0=79/50) and (gamma_0=1876/675), one explicit first-five-stage choice using the central interval is:

| (i) | (t_i) | (sigma_i) | (R_i) |
|---:|---:|---:|---:|
| 0 | 2 | 6 | (120064/18225) |
| 1 | 5 | 13 | (96591872/13286025) |
| 2 | 4 | 15 | (22245259264/3228504075) |
| 3 | 2 | 15 | (597199549696/87169610025) |
| 4 | 2 | 17 | (15905351014144/2353579470675) |

The recursion (2)–(4), not this finite sample, is the proof of arbitrary depth.


## 6. Quantitative linear lower bound on inverse depth

The preceding existence proof can be made quantitative. Fix (x_0=79/50), and make all band choices (t_i,\sigma_i) at (x_0) using the central interval. Write
[
\gamma_0(x)=\frac{884-512x}{27},\qquad
\gamma_{i+1}(x)=\lambda_i\gamma_i(x)-16\cdot2^{t_i-\sigma_i},
\qquad
\lambda_i=\frac{2^{t_i+2}}{3^{t_i+1}}.
]
At (x_0), (gamma_0=1876/675) and (|\gamma_0'|/\gamma_0=3200/469).

Since (t_i\in\{1,\ldots,5\}) and (R_i(x_0)\in(25/4,31/4)),
[
\frac{128}{2025}
\le\frac{\gamma_{i+1}(x_0)}{\gamma_i(x_0)}
=\lambda_i\frac{R_i(x_0)-4}{R_i(x_0)}
\le\frac{40}{93}<1.
	ag{5}
]
Also
[
\frac{|\gamma_{i+1}'(x_0)|}{\gamma_{i+1}(x_0)}
=\frac{R_i(x_0)}{R_i(x_0)-4}
\frac{|\gamma_i'(x_0)|}{\gamma_i(x_0)}
\le\frac{25}{9}
\frac{|\gamma_i'(x_0)|}{\gamma_i(x_0)}.
]
Consequently, with (C=24800/469),
[
|R_i'(x_0)|\le C(25/9)^i.
]
Choose
[
\delta_d=\frac{1}{16C}(9/25)^d.
	ag{6}
]
For every (i\le d) and (|x-x_0|\le\delta_d), this gives
[
|R_i(x)-R_i(x_0)|\le1/16.
	ag{7}
]

It remains to bound the finite-(K) error. Put (z_i=Z_i/2^K). Direct substitution in the seed formulas gives the exact identity
[
z_0=\gamma_0(x)+\frac{73-94K}{27\cdot2^K}.
]
Equation (3) gives
[
z_{i+1}=\lambda_i z_i-16\cdot2^{t_i-\sigma_i}
-\frac{2k_i+5}{2^K}.
	ag{8}
]
From (5), (gamma_i(x_0)\ge\gamma_0(128/2025)^i) and (gamma_i(x_0)\le\gamma_0). Hence
[
2^{\sigma_i}
=\frac{R_i(x_0)3^{t_i+1}}{\gamma_i(x_0)}
<2048(2025/128)^i<2048\cdot16^i,
]
and (sigma_i\ge0). Thus, for (i\le d), (|k_i|\le K+16+4d). Since (lambda_i\le8/9), iterating (8) yields the coarse bound
[
|z_i-\gamma_i(x)|
\le\frac{100(d+1)(K+20+4d)}{2^K}.
]
The exact source ratio at stage (i) differs from (R_i(x)) by at most
[
\frac{2^{\sigma_i}}{3^{t_i+1}}|z_i-\gamma_i(x)|
\le\frac{204800(d+1)(K+20+4d)16^d}{2^K}.
	ag{9}
]
For (a\ge12d+20) and (|x-x_0|\le\delta_d), we have (x>3/2), so
[
K\ge\frac34,2^a-4
\ge786432\cdot4096^d-4.
]
The right side of (9) is then less than (1/16) (and decreases rapidly with (K)). Combining this with (7), every exact source ratio lies in
[
(25/4-1/8,31/4+1/8)=(49/8,63/8).
]
For these large (K), (k_i\ge3), so the exact odd source-band inequalities with the (pm1) endpoints follow.

Finally, (L_d\le486\cdot3^{6d-1}=162\cdot729^d). The (K)-length of the interval (|x-x_0|\le\delta_d) is (delta_d2^a). If (a\ge12d+20), then
[
\frac{\delta_d2^a}{L_d}
\ge\frac{2^{20}}{2592C}
\left(\frac{4096}{2025}\right)^d>1,
]
because (C<53), (2^{20}>2592\cdot53), and (4096>2025). Thus the interval contains a representative of the Hensel-selected residue class modulo (L_d). We have proved the explicit corollary:

**For every integer (d\ge1) and every odd (a\ge12d+20), some (K\in\mathcal W) in the unique (9\mid Z_0) third-lift class has at least (d+2) successive odd ResetParent edges starting at (E).**

Equivalently, the maximum inverse-parent depth attained somewhere in the K-window grows at least linearly with (a), with this conservative explicit bound. This remains a statement across different (K) as (a) varies, not an infinite reverse path for one fixed target.

## Consequence

The unique third-lift class with (9\mid Z_0) has arbitrarily deep odd-parent ancestry for every sufficiently large odd (a). For (a\equiv0,1\pmod3), this class is one of the two non-high (Y\bmod27) lifts previously counted as excluded; for (a\equiv2\pmod3), it is the high-Y survivor. Thus the old 79/81 count is not a count of proved root exclusions for two-thirds of odd (a) classes. This construction does not imply root reachability for any fixed target, and the full fixed-parameter reverse cones remain open.
