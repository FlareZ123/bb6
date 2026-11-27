# A second all-depth inverse tower: valuation three and a 19-adic index bijection

**Agent 20, 27 November 2026. Status: complete arithmetic argument plus exact-integer regression; not yet Lean-kernel-certified or a blank-root statement.** This extends the independent 35-adic valuation-four tower in [Agent20's earlier report](../agent20-needle-four-tower/README.md). It is a new infinite prepared-predecessor phenomenon, not a decision of Space Needle or BB(6).

## Statement

For a positive integer \(r\), write the existing original-source-identified Space Needle cancellation terminal feeder's shifted counter as
\[
a_r=(9^r+5)/2,\quad A_r=2^{a_r},\quad
P_r(A)=(A-3)\sum_{i=0}^{r-1}A^{2(r-1-i)}9^i,\qquad B_r=2^{a_r-1}P_r(A_r).
\]
The exact identity is \(2(A_r+3)B_r=A_r(A_r^{2r}-9^r)\). A legal immediate valuation-**three** incoming edge into shifted target \(B\) is
\[
B=19q+30,\quad q\ge0,\qquad U(B)=8(2q+3)=\frac{16B-24}{19}. \tag{1}
\]
Its predecessor really has valuation three, since \(8(2q+3)\) has odd factor \(2q+3\).

**Theorem 1 (uniform 19-adic derivative).** For every \(k\ge1\) and \(r\ge1\) with \(r\equiv7\pmod9\), writing \(t_k=9\cdot19^{k-1}\),
\[
B_{r+t_k}\equiv B_r+12\cdot19^k\pmod{19^{k+1}}. \tag{2}
\]
The stronger base statement is
\[
B_r\equiv 6(6^r-9^r)\pmod{19}, \quad
B_r\equiv11\pmod{19}\quad\Longleftrightarrow\quad r\equiv7\pmod9. \tag{3}
\]
As 12 is a unit modulo 19, the map \(u\bmod19^k \mapsto B_{7+9u}\bmod19^{k+1}\) is a bijection onto all 19^k classes congruent to 11 modulo19.

**Theorem 2 (all-depth genuine prepared high-level histories).** For each \(k\ge1\) there exists a **unique** residue \(s_k\bmod t_k\), with \(s_1=7\bmod9\), such that
\[
U^k(B_r)\in\mathbb Z\quad\Longleftrightarrow\quad r\equiv s_k\pmod{t_k}
\qquad (r\ge1).\tag{4}
\]
For every \(r\ge k\) in this class, all k inverse steps are legal source-level Space Needle high-level valuation-three transitions (nonnegative q), before the established cancellation terminal edge. Thus every depth is realized on an infinite arithmetic progression of *prepared-input* terminal feeders. Nothing here proves that even one of those feeders belongs to the authentic blank-start orbit.

The first exact index classes are:

| k | s_k | period 9*19^(k-1) | target B modulo19^k |
|---:|---:|---:|---:|
| 1 | 7 | 9 | 11 |
| 2 | 25 | 171 | 353 |
| 3 | 196 | 3249 | 6851 |
| 4 | 39184 | 61731 | 130313 |
| 5 | 162646 | 1172889 | 2476091 |
| 6 | 15410203 | 22284891 | 47045873 |
| 7 | 193689331 | 423412929 | 893871731 |
| 8 | 4004405692 | 8044845651 | 16983563033 |
| 9 | 148811627410 | 152852067369 | 322687697771 |
| 10 | 1830184368469 | 2904189280011 | 6131066257793 |

## Proof of Theorem 1

For any integer c and k≥1 the elementary binomial induction yields
\[
(1+19c)^{19^{k-1}}\equiv1+c19^k\pmod{19^{k+1}}.\tag{5}
\]
Here \(2^{18}=1+19\cdot13797\), \(13797\equiv3\pmod{19}\), and \(9^9=1+19\cdot20390552\), \(20390552\equiv18\pmod{19}\). Thus, with \(t_k=9\cdot19^{k-1}\),
\[
2^{18\cdot19^{k-1}}\equiv1+3\,19^k,\quad
9^{t_k}\equiv1+18\,19^k\pmod{19^{k+1}}.\tag{6}
\]
For all positive r, \(9^r\equiv9\pmod{36}\), so \(a_r\equiv7\pmod{18}\) and \(A_r\equiv2^7\equiv14\pmod{19}\). The exponent increment \(a_{r+t_k}-a_r=9^r(9^{t_k}-1)/2\) is divisible by 19^k via (6); it is also divisible by 18 since \(a_r\equiv7\bmod18\). The factors are coprime, so it is divisible by \(18\cdot19^k\). Formula (5) with 2^18 then gives
\[
A_{r+t_k}\equiv A_r\pmod{19^{k+1}},\qquad
A_r^{2t_k}\equiv1+3a_r19^k\pmod{19^{k+1}}.\tag{7}
\]
The exact polynomial equation \(2(A_r+3)B_r=A_r(A_r^{2r}-9^r)\) and (6)-(7) imply
\[
B_{r+t_k}-B_r \equiv
19^k\frac{A_r}{2(A_r+3)}
(3a_r A_r^{2r}-18\cdot9^r)
\pmod{19^{k+1}}.\tag{8}
\]
Division in (8) denotes multiplication by the modular inverse: \(2(A_r+3)\equiv15\pmod{19}\), a unit. On the r=7 mod9 branch:
\[
9^r\equiv4,\quad a_r\equiv14,\quad
A_r\equiv14,\quad A_r^{2r}\equiv6^7\equiv9\pmod{19}.
\]
Hence \(A_r/[2(A_r+3)]\equiv6\) and the bracket is \(3\cdot14\cdot9-18\cdot4\equiv2\bmod19\), giving **6*2=12 mod19**. Formula (3) follows from the same exact identity modulo19: \(A_r\equiv14\) and the modular ratio is 6, so \(B_r\equiv6(6^r-9^r)\bmod19\). Both 6 and 9 have order 9 modulo19, and checking residues r=0,...,8 gives the unique value 11 at r=7. This establishes the induction base and the uniform unit derivative.

## Proof of Theorem 2, including actual predecessor legality

Set
\[
S_k=24\sum_{j=0}^{k-1}16^{k-1-j}19^j,\quad
C_k\equiv(16^k)^{-1}S_k\pmod{19^k}.\tag{9}
\]
The kth rational inverse is \((16^k B-S_k)/19^k\), so its integrality is equivalent to \(B\equiv C_k\bmod19^k\). For any j≤k the same congruence implies integrality of the jth rational inverse, since 19 is coprime to16 and the affine remainders nest.

From (3), k=1 has the unique index class s1=7 mod9. Suppose s_k is unique modulo \(t_k\). All possible lifts are \(s_k+j t_k\), j=0,...,18. Formula (2) says their B residues modulo19^(k+1) differ by exactly \(12j19^k\). Each is a distinct lift of C_k; consequently exactly one hits \(C_{k+1}\). The digit recursion is
\[
j_k\equiv8\frac{C_{k+1}-B_{s_k}}{19^k}\pmod{19},
\quad s_{k+1}=s_k+j_k t_k,\qquad
12^{-1}\equiv8\pmod{19}.\tag{10}
\]
This proves the all-k unique progression and constructs it explicitly, not by enumerating a finite cut.

Finally, \(P_r(A_r)\ge A_r-3\) and \(A_r\ge128\) imply \(B_r\ge A_r^2/4=2^{9^r+3}\ge64^r\). In particular for r≥k, \(B_r\ge19^k\). The affine inverse has fixed point -8:
\[
U^j(B)=\frac{16^j(B+8)-8\cdot19^j}{19^j}.
\]
For k≥2 its (k-1)st intermediate target is at least \(19\cdot16^{k-1}-8>30\), and all earlier targets are larger because \(U(y)<y\) for positive y. The k=1 case has B≥8000. Every predecessor step therefore starts at a genuine counter with q≥0, and the prescribed valuation-three source \(8(2q+3)\) is legal. This produces actual prepared-input high-level histories of arbitrary depth.

## Regression and scope

The independent [v3_tower_audit.py](v3_tower_audit.py) computes B modulo19^k directly from its defining finite geometric polynomial using logarithmic-time modular exponentiation, without assuming formula (8). It checks the complete first nine-residue class, verifies all twelve successive Hensel lifts and each slope 12, and includes direct integer evaluations for small r. A passed script is **not** a Lean proof; the preceding induction is a standalone mathematical derivation.

Agent46 previously source-certified infinite single valuation-three incoming edges for selected cancellation indices and three-predecessor fan-in families (see [their dossier](../agent46-needle-three/README.md)). This new result gives arbitrarily many **consecutive valuation-three edges into one prepared terminal feeder**, a different all-depth statement. It does not transfer the constructed histories to the authentic blank-start orbit nor establish BB(6)'s exact value. Keep it under \`im-results/\` pending a stronger root theorem or formal source check.
