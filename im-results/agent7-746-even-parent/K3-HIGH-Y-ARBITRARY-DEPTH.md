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

For every prescribed finite depth (d), there exist arbitrarily large odd (aequiv15pmod{162}) and integers (K) with (x\in\mathcal W), (K\equiv219pmod{486}), for which there is a chain of (d+2) genuine odd-arm (operatorname{ResetParent}) edges starting at (E).

The theorem does **not** assert that one fixed (E) has an infinite reverse path, or that any of these states is reachable from the authentic blank root (2). It asserts that no uniform finite inverse-depth cutoff can exclude this residue family as (a) varies.

## 1. Exact seed residue and the first two parents

The congruences
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
In particular (v_3(X)=1), (v_3(Y)=2), and (9\mid Z_0). The class is one of the non-high (Y\bmod27\in\{9,18\}) third-lift classes, not the (Y\equiv0\pmod{27}) survivor.

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

## 2. Base 3-adic isometry

The exact shift law derived in [K3-LOWER-T-PARENT-STRUCTURE.md](K3-LOWER-T-PARENT-STRUCTURE.md) is
[
Z_0(K+486\cdot3^s)
\equiv Z_0(K)+2\cdot3^{s+2}
\pmod{3^{s+3}}
qquad(s\ge0).
	ag{1}
]
For fixed (a\equiv15\pmod{162}) and (K\equiv219\pmod{486}), (9\mid Z_0(K)) throughout the progression. Thus, writing (K=K_0+486m),
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

Use the five-point band lemma from [NESTED-ODD-PARENT-HENSEL.md](NESTED-ODD-PARENT-HENSEL.md): for every (gamma>0), there are (t\in\{0,1,2,3,4\}) and (sigma\in\mathbb Z) such that
[
rac{gamma 2^\sigma}{3^{t+1}}\in(6,8).
]
Applying it to (gamma/3) instead gives the useful shifted form
[
t\in\{1,2,3,4,5\},qquad
R:=rac{gamma 2^\sigma}{3^{t+1}}\in(6,8).
	ag{2}
]

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
R_i=\frac{\gamma_i2^{\sigma_i}}{3^{t_i+1}}\in(6,8).
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
\longrightarrow R_i\in(6,8).
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
More strongly, any fixed open subinterval around (x_0=79/50) has (K)-length proportional to (2^a). Along (a=15+162n), this length tends to infinity. Therefore, for all sufficiently large (a) in this progression, the required residue cylinder modulo (L_d) has a representative with (x\) in that open subinterval. All source-band limits used above are then uniform for the finitely many stages (i\le d).

This supplies the required (K\inmathcal W) and completes the finite-depth construction.

For reference, the first five exact leading-coefficient choices at (x_0=79/50) can be taken as
[
(t_i,\sigma_i)=(2,6),(2,8),(1,9),(1,10),(3,15),
]
with corresponding (R_i) approximately
[
6.58787,quad6.13422,quad7.58834,quad6.37926,quad7.51965.
]
The recursion (2)–(4), not this finite sample, is the proof of arbitrary depth.

## Consequence

The K3 high-(Y) non-high third-lift class (a\equiv15\pmod{162}), (K\equiv219\pmod{486}) has arbitrarily deep odd-parent ancestry as the parameters vary. Therefore the claimed immediate parentlessness of this class is false, and a bounded-depth argument uniform in (a) cannot close it. The original 79/81 root-exclusion claim still requires a separate analysis of all reverse branches for each fixed parameter; this theorem does not imply root reachability.
