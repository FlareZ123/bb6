# Second-level predecessor sieve for the valuation-two cancellation family

## Correction record (2026-11-14)

Two independent errors affected the original second-level prime sieve. On the p=5 cylinder \(w\equiv0\pmod4\), the parent equation forces \(w\equiv4\pmod5\), so \(w\equiv4\pmod{20}\) must be retained; see [Agent 48's p=5 audit](../agent48-needle-sieve-audit/SecondLevelPrime5Correction.md). On the p=13 cylinder \(w\equiv9\pmod{12}\), the parent equation forces \(w\equiv12\pmod{13}\), rather than excluding the whole cylinder; the derivation and exact recount are in [SecondLevelPrime13Correction.md](SecondLevelPrime13Correction.md).

With the p=5 and p=13 congruence corrections applied, the eight-prime baseline is 38.50383574%. A further CRT-normalization audit found that the eleven-prime extension had counted p=13 twice: 900900 already contains 13 through the modulus-39 cylinder. The corrected eleven-prime density is 36.51713603%; the separate conditional \(11^2\) refinement remains 38.24667388%. These are candidate-valuation densities only and do not establish an actual predecessor or blank-root reachability. The correction and exact reconciliation are recorded in [SecondLevelPrime13Correction.md](SecondLevelPrime13Correction.md).

## 1. The second-level target

Put
\[
r=110j+50,\qquad a=\frac{9^r+5}{2},\qquad A=2^a,\qquad P=P_r(A),
\]
where
\[
P_0(A)=0,\qquad P_{k+1}(A)=A^2P_k(A)+9^k(A-3).
\]

The existing valuation-two source theorem supplies a parameter \(p\) with
\[
AP+3-4=11(2p+3),
\]
hence
\[
AP=22p+34.
\]

Because \(10\mid r\), we have \(9^r\equiv1\pmod{40}\), so \(a\equiv3\pmod{20}\) and \(A\equiv8\pmod{25}\). Also \(9^r\equiv1\pmod{25}\) and \(A^{2r}\equiv8^{2r}\equiv1\pmod{25}\), since \(20\mid2r\). The exact identity
\[
(A+3)P+9^r=A^{2r}
\]
therefore gives \(11P\equiv0\pmod{25}\), hence \(P\equiv0\pmod{25}\). Thus \(AP\equiv0\pmod{25}\), and \(AP=22p+34\) gives
\[
p\equiv3\pmod{25}.
\]

Consequently
\[
p_0=\frac{8p+6}{5}\in\mathbb N,\qquad y=2p_0+3
\]
are well-defined, and the source transition has the two-edge ancestry
\[
\operatorname{oddTower}(p_0,0)\longrightarrow
\operatorname{oddTower}(p,2)\longrightarrow
\text{the valuation-two cancellation feeder}.
\]
A direct calculation gives the useful target identity
\[
\boxed{55y=8AP+25.}
\]
In particular, \(5\mid y\).

For an incoming source \(\operatorname{oddTower}(q,w)\) of \(\operatorname{oddTower}(p_0,0)\), the exact inverse-parent equation from NeedleGeneralInverse is
\[
y=(2^{w+1}+3)q+3\cdot2^w+w+3. \tag{1}
\]
Write \(D_w=2^{w+1}+3\) and \(b_w=3\cdot2^w+w+3\).

## 2. Target-specific prime cylinders

Let
\[
B=\frac{AP}{2}=11p+17.
\]
Then
\[
55y=16B+25. \tag{2}
\]
If a prime \(p_*\) divides \(D_w\), equation (1) forces \(y\equiv b_w\pmod{p_*}\). Applying this to the established prime moduli \(5,7,11,13,19,29,37,61,67,79,101\) gives the following necessary conditions on every predecessor valuation.

| Prime | Divisibility cylinder for \(D_w\) | Necessary condition on \(w\) |
|---|---|---|
| \(5\) | \(w\equiv0\pmod4\) | \(w\equiv4\pmod5\) (equivalently \(w\equiv4\pmod{20}\)) |
| \(7\) | \(w\equiv1\pmod3\) | \(w\equiv c_7(j)\pmod7\) |
| \(11\) | \(w\equiv2\pmod{10}\) | \(w\equiv9-j\pmod{11}\) |
| \(13\) | \(w\equiv9\pmod{12}\) | \(w\equiv12\pmod{13}\) |
| \(19\) | \(w\equiv3\pmod{18}\) | \(w\equiv c_{19}(j)\pmod{19}\) |
| \(29\) | \(w\equiv18\pmod{28}\) | \(w\equiv c_{29}(j)\pmod{29}\) |
| \(61\) | \(w\equiv35\pmod{60}\) | \(w\equiv c_{61}(j)\pmod{61}\) |
| \(67\) | \(w\equiv5\pmod{66}\) | \(w\equiv c_{67}(j)\pmod{67}\) |
| \(37\) | \(w\equiv7\pmod{36}\) | \(w\equiv c_{37}(j)\pmod{37}\) |
| \(79\) | \(w\equiv9\pmod{39}\) | \(w\equiv c_{79}(j)\pmod{79}\) |
| \(101\) | \(w\equiv18\pmod{100}\) | \(w\equiv c_{101}(j)\pmod{101}\) |

The parameter-dependent forced residues are:

\[
\begin{array}{c|ccc}
j\bmod3&0&1&2\\ \hline
y\bmod7&1&5&3\\
c_7(j)&6&3&1\\
y\bmod61&60&30&6\\
c_{61}(j)&31&1&38
\end{array}
\]

\[
\begin{array}{c|rrrrrrrrr}
j\bmod9&0&1&2&3&4&5&6&7&8\\ \hline
y\bmod19&12&4&16&10&17&16&7&8&16\\
c_{19}(j)&4&15&8&2&9&8&18&0&8
\end{array}
\]

\[
\begin{array}{c|rrrrrrrrrrrrrrrrrrrrr}
j\bmod21&0&1&2&3&4&5&6&7&8&9&10&11&12&13&14&15&16&17&18&19&20\\ \hline
y\bmod29&15&1&22&9&27&11&26&25&15&21&14&27&25&26&8&8&5&22&27&20&26\\
c_{29}(j)&2&17&9&25&14&27&13&12&2&8&1&14&12&13&24&24&21&9&14&7&13
\end{array}
\]

For prime 67, the additional period-three residues are \(y\bmod67=(29,20,22)\) and \(c_{67}(j)=(64,55,57)\) for \(j\bmod3=(0,1,2)\). Here the forced-residue functions are: The additional forced-residue tables are \(c_{37}=(14,36,7,13,10,4,31,12,10)\) (period \(9\)), \(c_{79}=(74,37,5,47,56,12,31,49,34,63,19,32,67,42,67,4,37,59,44,22,15,5,63,13,42,53,35,64,16,42,41,73,18,22,60,63,78,55,29)\) (period \(39\)), and \(c_{101}=(80,90,73,38,18)\) (period \(5\)).
\[
c_7(j)=y-2\pmod7,\quad
c_{19}(j)=y-8\pmod{19},\quad
c_{29}(j)=y-13\pmod{29},\quad
c_{61}(j)=y-29\pmod{61},\quad c_{67}(j)=y-32\pmod{67}.
\]

### Derivation checkpoints

- **Prime 5.** From (2), \(y\equiv0\pmod5\). If \(w\equiv0\pmod4\), then \(2^w\equiv1\pmod5\), so the coefficient \(2^{w+1}+3\) vanishes modulo 5 and the parent equation reduces to \(0\equiv w+6\pmod5\). Thus this cylinder forces \(w\equiv4\pmod5\): exactly \(w\equiv0,8,12,16\pmod{20}\) are excluded, while \(w\equiv4\pmod{20}\) must be retained. In particular, \(w=24\) survives this filter and all other listed prime cylinders.
- **Prime 7.** The existing sourceB_mod35 calculation gives \(B\bmod35=0,20,15\) according as \(r\bmod3=0,1,2\). Equation (2) gives \(y\bmod7=3,5,1\) in those three cases. Since \(w\equiv1\pmod3\) implies \(b_w\equiv w+2\pmod7\), the forced residues are \(6,3,1\) for \(j\bmod3=0,1,2\).
- **Prime 11.** Put \(v=(9^r+3)/2=a-1\). Since \(10\mid r\), \(v\equiv2\pmod{110}\), so \(A\equiv8\) and \(2^v\equiv4\pmod{121}\). With \(G_k=\sum_{i=0}^{k-1}64^{k-1-i}9^i\), the recurrence gives \(G_{110}\equiv66\) and \(P_{50}\equiv7\pmod{121}\). The 110-step recurrence therefore yields
  \[
  P_{110j+50}\equiv7+88j\equiv7-33j\pmod{121}.
  \]
  Hence \(B\equiv28-11j\pmod{121}\), and (2) gives \(y\equiv2-j\pmod{11}\). On \(w\equiv2\pmod{10}\), \(b_w\equiv w+4\pmod{11}\), giving \(w\equiv9-j\pmod{11}\).
- **Prime 13.** Here \(v\equiv6\pmod{12}\), so \(A\equiv11\pmod{13}\) and \(A^2\equiv4\). Since \(r=110j+50\) is even, \(4^r\equiv9^r\pmod{13}\); the closed polynomial identity therefore gives \(P\equiv0\pmod{13}\), and (2) yields \(y\equiv4\pmod{13}\). On the denominator cylinder \(w\equiv9\pmod{12}\), \(2^w\equiv5\pmod{13}\), so \(b_w=3\cdot2^w+w+3\equiv w+5\pmod{13}\). Thus the parent equation forces \(w\equiv12\pmod{13}\); the cylinder is not impossible.
- **Prime 19.** Since \(9^r\equiv9\pmod{36}\), \(v\equiv6\pmod{18}\), \(A\equiv14\), and \(2^v\equiv7\pmod{19}\). The geometric-sum identity gives \(B\equiv G_r(6,9)\equiv6(6^r-9^r)\pmod{19}\). Substitution into (2) gives the nine-entry table above. On \(w\equiv3\pmod{18}\), \(b_w\equiv w+8\pmod{19}\).
- **Prime 29.** Reusing the established first-level residues \(A\bmod29=8,12,27\) according as \(r\bmod3=0,1,2\), evaluate
  \[
  P\equiv(A-3)(A^{2r}-9^r)(A^2-9)^{-1}\pmod{29},
  \qquad B\equiv AP/2.
  \]
  Equation (2) gives the displayed period-21 table. Since \(2^{18}\equiv13\pmod{29}\), the cylinder \(w\equiv18\pmod{28}\) forces \(w\equiv y-13\pmod{29}\).
- **Prime 61.** Since \(r\) is even, the established residues are \(A\equiv43\) and \(P\equiv4(19^r-9^r)\pmod{61}\). Equation (2) gives the period-three table. Since \(2^{35}\equiv29\pmod{61}\), the cylinder \(w\equiv35\pmod{60}\) forces \(w\equiv y-29\pmod{61}\).

- **Prime 67.** Modulo \(1320\), \(9^{50}\equiv9^{110}\equiv441\) and \(441^2\equiv441\), so \(v=(9^r+3)/2\equiv222\pmod{660}\). Hence \(A\equiv2373\) and \(2^v\equiv3029\pmod{3685}\). The recurrence has \(A^2\equiv449\), \(A-3\equiv2370\), \(G_{110}\equiv2420\), \(A^{220}\equiv3521\), and \(9^{50}\equiv2476\pmod{3685}\). Thus
  \[
  P_{r+110}\equiv3521P_r+2750\pmod{3685},\qquad P_{50}\equiv2020,
  \]
  giving \(P_{50},P_{160},P_{270}\equiv2020,3120,3285\). Consequently \(B\equiv1480,2140,765\) and \(y\bmod67=29,20,22\) for \(j\bmod3=0,1,2\). Since \(2^6\equiv-3\pmod{67}\), the cylinder is \(w\equiv5\pmod{66}\); there \(b_w\equiv w+32\pmod{67}\), forcing \(w\bmod67=64,55,57\).

- **Primes 37, 79, and 101.** For each prime let \(M=55p\) and \(T(A)=\begin{pmatrix}A^2&A-3\\0&9\end{pmatrix}\pmod M\); then \(P_r(A)\) is the upper-right entry of \(T(A)^r\). For \(p=37\), \(9^r\equiv81\pmod{360}\), so \(A\equiv1053\pmod{2035}\), and \(T(1053)^{990}=I\); this gives period \(9\) and the \(c_{37}\) table above. For \(p=79\), \(9^r\bmod1560\) cycles \(81,321,1041\), giving \(A\)-cycle \(1438,4078,3363\); each corresponding \(T(A)^{4290}=I\pmod{4345}\), giving period \(39\) and the \(c_{79}\) table. For \(p=101\), \(9^r\equiv1\pmod{200}\), so \(A\equiv8\pmod{5555}\), and \(T(8)^{550}=I\); this gives period \(5\) and the \(c_{101}\) table. Their denominator cylinders follow from \(2^8\equiv-3\pmod{37}\), \(2^{10}\equiv-3\pmod{79}\), and \(2^{19}\equiv-3\pmod{101}\).

These are necessary conditions, not sufficient conditions for a predecessor. In particular, the \(w=0,1,2,3,4,5\) classification follows immediately: \(w=0\) is impossible; \(w=1\) is possible exactly for \(j\equiv2\pmod3\); \(w=2\) is possible exactly for \(j\equiv7\pmod{11}\); \(w=3,4,5\) are impossible.

### Exact density of the eight-prime filter

All base cylinders are determined by \(w\bmod13860\), where
\[
13860=\operatorname{lcm}(4,12,3,10,18,28,60,66).
\]
For each base residue \(b\bmod M_0\), apply the corrected p=5, p=7, and p=11 guards and impose the p=13 forced residue directly: if \(b\equiv9\pmod{12}\), require \(b\equiv12\pmod{13}\). This is a direct base-residue filter because 13 already divides \(M_0\) through the modulus-39 cylinder. Do not add a second independent factor of 13. Each active cylinder among \(19,29,37,61,67,79,101\) contributes one residue modulo its prime, otherwise all prime residues remain.
\[
L_{11}=900900\cdot19\cdot29\cdot37\cdot61\cdot67\cdot79\cdot101
=598\,939\,578\,493\,155\,900
\]
and, for every \(j\bmod33\), exactly
\[
218\,715\,580\,637\,067\,540
\]
surviving residues. Therefore the corrected eleven-prime necessary sieve leaves
\[
\boxed{\frac{4\,596\,796\,566\,563}{12\,588\,053\,352\,105}
\approx0.3651713603.}
\]
It eliminates about \(63.48286\%\) of valuation classes. The corrected CRT count and the additional odd-block history filter are reproducible in second_level_eleven_prime_density.js; the latter is derived in [SecondLevelOddBlockFilter.md](SecondLevelOddBlockFilter.md). The forced-residue and matrix-period certificates for the new primes are in second_level_extra_prime_tables.js.
## 3. A uniform high-side middle-band exclusion

The prime cylinders leave many valuations. There is also a large contiguous interval, depending on \(r\), that can be excluded without any prime-specific residue table.

Let
\[
\nu=3^{2r-1},\qquad
d=1+\lfloor\log_2\nu\rfloor.
\]
The odd-gap lemma gives
\[
2^d\ge\nu+5.
\]
Indeed, \(2^d-\nu\) is positive and odd; it cannot be 1 because \(3^{2r-1}+1\) has a nontrivial odd factor, and it cannot be 3 because \(3^{2r-1}+3\) is divisible by 3.

**Theorem.** Suppose \(r\ge2\), \(55y=8AP+25\), and \(s\in\mathbb N\) satisfies
\[
s\ge d+6,\qquad
(2r-2)s\le a-d-6.
\]
Then there is no \(q\in\mathbb N\) satisfying
\[
\boxed{
y=(2^{a+s}+3)q+3\cdot2^{a+s-1}+a+s+2.
} \tag{3}
\]
Equivalently, no immediate predecessor of \(\operatorname{oddTower}(p_0,0)\) can have valuation
\[
w=a+s-1
\]
in the interval
\[
\boxed{
a+d+5\le w\le
a+\left\lfloor\frac{a-d-6}{2r-2}\right\rfloor-1.
}
\]

### Proof

Set \(t=2^s\) and
\[
S=\sum_{i=0}^{2r-1}t^i.
\]
Then \((t-1)S=t^{2r}-1\), so
\[
S(t-1)<t^{2r}. \tag{4}
\]

The parent equation (1), with \(w=a+s-1\), implies
\[
D=2^{a+s}+3\mid 2y+3-2w.
\]
Multiplying by 55 and using \(55y=8AP+25\) gives
\[
D\mid16AP+215-110w=16AP-C,
\]
where
\[
C=55\cdot9^r+110s-50.
\]
The band hypotheses imply \(s\le a\), hence
\[
16\cdot9^r<C<330\nu+275. \tag{5}
\]

We need one exact polynomial certificate. Define \(S_0=K_0=0\), and recursively
\[
S_{m+1}=S_m+t^{2m}+t^{2m+1},
\]
\[
K_{m+1}=(At)^2K_m
 +3^{2m}(At-3)S_m
 +9^m t^{2m}\bigl(t(A-3)-3\bigr).
\]
Induction using
\[
(At+3)(At-3)=(At)^2-9
\]
and
\[
(At+3)\bigl(t(A-3)-3\bigr)+9(1+t)=t^2A(A-3)
\]
proves
\[
t^{2m}AP_m(A)=3^{2m}S_m+(At+3)K_m.
\]
At \(m=r\), \(S_r=S\) and \(At+3=D\). Therefore
\[
D\mid Q,\qquad
Q=Ct^{2r}-E,\qquad
E=16\cdot3^{2r}S. \tag{6}
\]
Also \(Q>0\), because \(C>16\cdot9^r\) and \(S<t^{2r}\).

Use the elementary small-deficit fact: if \(D=B+3\), \(E'>0\), \(E'\le Bh\), and \(E'+3h<D\), then
\[
D\nmid Bh-E'.
\]
Indeed, \(Bh-E'=Dh-(E'+3h)\), so divisibility would force the positive integer \(E'+3h\) to be a multiple of \(D\) smaller than \(D\).

Put \(B=2^{a+s}\). The band hypotheses give
\[
t\ge64(\nu+5),\qquad
2^m\ge64(\nu+5),\qquad
m=a-(2r-2)s.
\]
In particular, \(u=t-1\ge63(\nu+5)\) and \(t/u\le64/63\). From (4) and \(9^r=3\nu\),
\[
E=48\nu S.
\]

There are two cases.

**Case 1: \(2rs\le a+s\).** Let \(k=a+s-2rs\), \(h=C\), and \(E'=2^kE\). Then
\[
2^kQ=Bh-E',
\]
so (6) implies \(D\mid Bh-E'\). But
\[
\frac{21E'}B
=\frac{1008\nu S}{t^{2r}}<16,
\]
using \(Su<t^{2r}\) and \(u>63\nu\). Also \(B\ge t^2\ge4096(\nu+5)^2\), and (5) gives
\[
\frac{21\cdot3h}{B}
=\frac{63C}{B}<1,
\]
since
\[
63(330\nu+275)<4096(\nu+5)^2.
\]
Thus \(E'+3h<B+3=D\), while \(0<E'\le Bh\), contradicting the small-deficit fact.

**Case 2: \(2rs\ge a+s\).** Let \(k=2rs-a-s\), \(h=C2^k\), and \(E'=E\). Again
\[
Q=Bh-E',
\]
so \(D\mid Bh-E'\). Put \(m_2=a-(r-1)s=(a+m)/2\ge m\). From (4),
\[
\frac{21E'}B
<\frac{1008\nu\,t}{2^m u}
\le\frac{1008\nu}{63(\nu+5)}<16.
\]
Also
\[
\frac{21\cdot3h}{B}
=\frac{63C}{2^{2m_2}}<1,
\]
by \(2^{m_2}\ge2^m\ge64(\nu+5)\) and (5). Thus once more \(E'+3h<B+3=D\) and \(0<E'\le Bh\), a contradiction.

Both cases are impossible, proving (3). \(\square\)

The interval is nonempty for every \(r\ge2\). For example, \(d\le4r-3\); for \(r\ge3\), \(9^r\ge32r^2\), giving \(a\ge16r^2\ge(2r-1)(d+6)\), and \(r=2\) is immediate.

For the first member \(r=50\) of the actual source progression:
\[
d=157,\quad
s_{\min}=163,\quad
s_{\max}=2629477146591894546104393519212353432153609804.
\]
Thus the theorem excludes every predecessor valuation in the contiguous interval
\[
257688760366005665518230564882810636351053761165
\le w\le
260318237512597560064334958402022989783207370806.
\]

## 4. Low-side quotient bands

The high-side theorem treats \(w>a\). There is a complementary family below \(a\). For any candidate valuation \(w<a\), write
\[
a=k(w+1)+s,\qquad k\ge1,\quad s\ge0.
\]
The quotient \(k\) and remainder \(s\) are uniquely determined by \(w\).

**Theorem.** Suppose \(r\ge2\), \(55y=8AP+25\), and
\[
a=k(w+1)+s,\qquad k\ge1,\quad s\ge0,
\]
If
\[
\boxed{a>(2rk+1)s+4rk^2+6k,} \tag{7}
\]
then no \(q\in\mathbb N\) satisfies the parent equation (1) at valuation \(w\).

**Proof.** Put \(D=2^{w+1}+3\). As before, a parent would force
\[
D\mid16AP+215-110w. \tag{8}
\]
Since \(2^{w+1}\equiv-3\pmod D\) and \(a=k(w+1)+s\),
\[
A=2^a\equiv2^s(-3)^k\pmod D.
\]
The polynomial identity
\[
P_r(A)=\sum_{j=0}^{2r-1}(-3)^jA^{2r-1-j}
\]
therefore gives
\[
AP\equiv3^{2r}S\pmod D,\qquad
S=\sum_{\ell=1}^{2r}X^\ell,\qquad
X=(-3)^{k-1}2^s.
\]
Thus \(D\) divides
\[
R=16\cdot3^{2r}S+215-110w. \tag{9}
\]

The hypothesis (7), after substituting \(a=k(w+1)+s\), is exactly
\[
w>2rs+4rk+5. \tag{10}
\]
In particular \(w\ge14\).

The boundary case \(k=1,s=0\) is now handled directly. Here \(w=a-1\) and \(D=2^a+3=A+3\), so \(A\equiv-3\pmod D\). The polynomial expansion gives
\[
AP\equiv 2r\,3^{2r}\pmod D.
\]
If a parent existed, (8) would therefore imply
\[
D\mid (32r-55)9^r+50.
\]
For \(r\ge2\), this integer is positive. Also \(9^r\ge10r+7\), so \(a=(9^r+5)/2\ge5r+6\). Since \(r<2^r\) and \(9^r<2^{4r}\),
\[
0<(32r-55)9^r+50<32r9^r+50<2^{5r+6}\le2^a<D,
\]
a contradiction.

Hence assume \((k,s)\ne(1,0)\), and put \(Y=3^{k-1}2^s=|X|\). Now \(Y\ge2\). The geometric-sum bound gives \(|S|\le2Y^{2r}\). Hence
\[
|16\cdot3^{2r}S|
\le32\cdot3^{2rk}2^{2rs}
<2^{5+4rk+2rs}<2^w,
\]
where the last inequality is (10) and \(3<4\). Since \(w\ge14\), also \(|215-110w|<2^w\). Consequently
\[
|R|<2^{w+1}<D. \tag{11}
\]

It remains to show \(R>0\). If \(k\) is odd, then \(X=Y\ge2\), so \(S\ge2r\). Therefore
\[
R\ge32r\cdot9^r+215-110w
\ge(32r-55)9^r-60>0,
\]
using \(w\le a-1\) and \(110a=55\cdot9^r+275\). If \(k\) is even, then \(X=-Y\), with \(Y\ge3\), and
\[
S=\frac{Y(Y^{2r}-1)}{Y+1}\ge\frac{Y^{2r}}2.
\]
Thus
\[
R\ge8\cdot3^{2rk}2^{2rs}+215-110w
\ge8\cdot3^{4r}-55\cdot9^r-60>0.
\]
The final inequality holds for every \(r\ge2\). In either parity case, (9) and (11) give \(0<R<D\), contradicting \(D\mid R\). \(\square\)

For fixed \(k\), condition (7) is equivalent to
\[
0\le s\le
s_{\max}(k):=
\left\lfloor\frac{a-4rk^2-6k-1}{2rk+1}\right\rfloor,
\qquad s\equiv a\pmod k.
\]
The boundary \(k=1,s=0\) is included by the direct argument above. Since \(s\) advances in steps of \(k\), each nonempty quotient class gives a contiguous interval of excluded \(w=(a-s)/k-1\).

For \(r=50\), the first two low-side bands are:
\[
\begin{aligned}
k=1:\quad&
255137386500995708433891648398822412228766100005\\
&\le w\le
257688760366005665518230564882810636351053761002,\\[2mm]
k=2:\quad&
128203363366171972894642072081000316592564060202\\
&\le w\le
128844380183002832759115282441405318175526880500.
\end{aligned}
\]
The direct boundary argument closes the former one-valuation gap \(w=a-1\). For \(r=50\), the \(k=1\) low-side band now ends at \(a-1\), while the \(k=0\) large-remainder band in Section 5 begins at \(a\). Their union is therefore contiguous across \(a-1,a\). Middle-remainder quotient classes outside all bands still require separate treatment.

## 5. Large-remainder quotient bands

There is a complementary exclusion when the quotient remainder \(s\) is close to its maximum \(w\). Write
\[
a=(k+1)(w+1)-d,\qquad k\ge0,\quad 1\le d\le w.
\]
Equivalently, in the quotient representation \(a=k(w+1)+s\), we have \(s=w+1-d\).

**Theorem.** Suppose \(r\ge3\), \(a=(k+1)(w+1)-d\), \(k\ge0\), \(1\le d\le w\), \(w\ge2rd\), and
\[
\boxed{
2^{\,w-2rd}>
\max\!\left\{110w,\;32r\,2^{4r(k+1)}\right\}.
} \tag{12}
\]
Then no \(q\in\mathbb N\) satisfies the parent equation (1) at valuation \(w\).

**Proof.** Put \(D=2^{w+1}+3\). A parent still forces
\[
D\mid16AP+215-110w. \tag{13}
\]
Since \(2^{w+1}\equiv-3\pmod D\) and \(a=(k+1)(w+1)-d\),
\[
2^dA\equiv(-3)^{k+1}\pmod D.
\]
Using the polynomial expansion for \(P_r\) from Section 4 and multiplying by \(2^{2rd}\), we obtain
\[
2^{2rd}AP\equiv3^{2r}T\pmod D,
\qquad
T=\sum_{\ell=1}^{2r}(-3)^{k\ell}2^{(2r-\ell)d}.
\]
Thus (13) implies \(D\mid R\), where
\[
R=16\cdot3^{2r}T-(110w-215)2^{2rd}. \tag{14}
\]

The final summand of \(T\) is odd and every earlier summand is even, so \(T\) is odd. Hence the first term of \(R\) has exact 2-adic valuation \(4\). The second term has exact 2-adic valuation \(2rd\ge6\), since \(110w-215\) is odd. Therefore \(R\ne0\).

For the size bound, each summand of \(T\) has absolute value at most \(3^{2rk}2^{2rd}\), so
\[
|16\cdot3^{2r}T|
\le32r\cdot3^{2r(k+1)}2^{2rd}
<32r\cdot2^{4r(k+1)}2^{2rd}
<2^w.
\]
The other term satisfies
\[
|(110w-215)2^{2rd}|
<110w\,2^{2rd}<2^w.
\]
Consequently \(0<|R|<2^{w+1}<D\), contradicting \(D\mid R\). \(\square\)

For fixed \(k\), the relation \(a=(k+1)(w+1)-d\) requires \(d\equiv-a\pmod{k+1}\); as \(d\) increases by \(k+1\), \(w\) increases by one. The condition (12) is monotone decreasing in \(d\), so each nonempty class gives one contiguous excluded interval.

For \(r=50\), the first three intervals are:
\[
\begin{aligned}
k=0:\quad&
257688760366005665518230564882810636351053761003\\
&\le w\le
260291677137379460119424813012940036718236122222,\\[1mm]
k=1:\quad&
128844380183002832759115282441405318175526880501\\
&\le w\le
129491839379902344481522896926035495653795859797,\\[1mm]
k=2:\quad&
85896253455335221839410188294270212117017920334\\
&\le w\le
86183531894985172414123934743414928545502930098.
\end{aligned}
\]
For \(k=0\), this band overlaps the high-side certificate of Section 3 and fills its lower-end gap. Their union excludes the entire contiguous interval
\[
a\le w\le
260318237512597560064334958402022989783207370806
\qquad(r=50).
\]
For \(k\ge1\), the large-remainder bands complement the low-side small-remainder bands of Section 4. In particular, for \(r=50\), the \(k=1\) large-remainder band begins immediately after the \(k=2\) low-side band ends, at the quotient boundary near \(a/2\); the same adjacent-boundary phenomenon occurs near \(a/3\).

## 6. What this resolves—and what it does not

For the second-level target, the current exact restrictions are:

1. \(w=0,3,4,5\) are impossible.
2. \(w=1\) survives the necessary divisibility condition only when \(j\equiv2\pmod3\).
3. \(w=2\) survives the necessary divisibility condition only when \(j\equiv7\pmod{11}\).
4. The corrected eight-prime baseline leaves \(38.50383574\%\) of candidate valuation classes. Adding \(37,79,101\) gives an eleven-prime density of \(36.51713603\%\). The separate corrected \(11^2\) refinement leaves \(38.24667388\%\) when \(j\equiv10\pmod{11}\); it has not been combined with the eleven-prime sieve.
5. The high-side certificate and the \(k=0\) large-remainder theorem exclude a contiguous interval beginning at \(w=a\) for \(r=50\). The low-side theorem now also excludes the boundary \(w=a-1\), so its \(k=1\) interval joins that \(k=0\) interval. The other low-/large-remainder bands meet near the quotient boundaries \(a/2,a/3,\ldots\). Middle-remainder classes outside these bands remain.
6. The mod-5 odd-block filter leaves only \(4.04464726\%\) of all valuation classes whose parent source can have an odd predecessor. The mod-25 classification in [SecondLevelOddBlockFilter.md](SecondLevelOddBlockFilter.md) determines exactly which of those sources can have an odd block of length at least two. All other odd-entry candidates have an odd block of exactly one transition; their odd predecessor must itself have an even predecessor. If that predecessor has valuation \(t\ge1\), it must satisfy
   \[
   2^{t+1}+3\mid4b+21-10t.
   \]

These are necessary-condition results for the ancestry of the second-level target. They do **not** prove that every candidate parent is impossible, and they do not establish blank-root reachability or an upper bound for BB(6). The next high-value work is to exploit the forced-even divisibility condition above and attack the remaining middle-remainder quotient classes, rather than repeat the settled prime-cylinder filters.

Relevant source components:
- im-results/agent20-needle-coprime/CancellationParentTwoSource.lean
- im-results/agent20-needle-coprime/NeedleGeneralInverse.lean
- im-results/agent47-needle-cancellation-parent4/NeedleCancelMod35.lean
- im-results/agent46-needle-midstrip/README.md
- im-results/agent20-needle-coprime/SecondLevelOddBlockFilter.md



## 7. Wider residue-cut band above \(a\)

The new [SecondLevelWideResidueCut.md](SecondLevelWideResidueCut.md) theorem extends the high-side analysis. For \(w=a+s-1\), it excludes every \(s\) satisfying
\[
(2r-1)s\ge a,\qquad (r-1)s\le a-d-3,\qquad
((a+s-5)\bmod s)+1\ge d,
\]
where \(d=1+\lfloor\log_2(3^{2r-1})\rfloor\). The complementary residue failures are exactly parametrized by
\[
a-5=ks+e,\quad r-1\le k\le2r-2,\quad 0\le e\le d-2,
\]
so there are at most \(r(d-1)\) exceptions. The companion BigInt audit intersects these exceptions with the existing eleven-prime filter and the \(t=1,\ldots,7\) two-step conditions.

This is an arithmetic exclusion for a wide band above \(a\), not a closure of the remaining \(w<a\) middle-remainder classes. The proof is not yet Lean-formalized or composed with the pinned original-source inverse theorem. The finite audit is not a reachability proof.
