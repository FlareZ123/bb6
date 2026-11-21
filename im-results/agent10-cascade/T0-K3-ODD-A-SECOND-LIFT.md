# Odd-a K ≡ 3 (mod 6): second-lift 25-of-27 exclusion

**Status:** paper-level continuation of [the seven-of-nine phase theorem](T0-K3-ODD-A-SEVEN-OF-NINE.md). The finite modulo-81 table below is checked by the accompanying exact script. The parent-gap arguments are exact inequalities against the source ResetParent bands, but this continuation has not been Lean-formalized or independently reviewed. It remains in im-results.

## Theorem

Let \(a\ge13\) be odd, \(K\equiv3\pmod6\), and
\[
x=\frac{2K+7}{2^a}\in
\mathcal W:=
\left[\frac{803}{512},\frac{415}{256}-\frac1{1024}\right].
\tag{1}
\]
Use the t=0 auxiliary entry \(E\), phase variable \(X=2E+5\), and notation from the preceding theorem. The interval \(\mathcal W\) is contained in the earlier source window \([97/64,13/8]\). Its width as an interval for \(K\) is
\[
\frac{53\cdot2^a}{2048}>162
\qquad(a\ge13).
\tag{2}
\]
Thus, for every fixed \(a\), it contains representatives of all three lifts modulo \(162\) of every allowed residue modulo \(54\).

For each fixed odd \(a\), the 27 residue classes \(K\bmod162\) satisfying \(K\equiv3\pmod6\) split as follows:
- all three lifts of seven of the nine \(K\bmod54\) phases are root-excluded by the first theorem;
- in the \(X\equiv0\pmod9\) phase, two of the three \(K\bmod162\) lifts are root-excluded;
- in the \(X\equiv3\pmod9\) phase, two of the three \(K\bmod162\) lifts are root-excluded on \(\mathcal W\).

Therefore **25 of the 27 \(K\bmod162\) classes are root-excluded** for the t=0 auxiliary entry \(E\). Exactly two classes remain as higher-valuation possibilities, one in each exceptional \(K\bmod54\) phase. This is still an auxiliary-entry result, not an exclusion of the fatal target or its other inverse branches.

## 1. Why the second lift is indexed by K modulo 162

Write
\[
T=80\cdot2^K+2K+13-2(2K+7)2^{K+4-a},
\qquad X=T/3.
\tag{3}
\]
To compute \(X\bmod27\), reduce \(T\bmod81\). Modulo \(81\), the powers \(2^K\) and \(2^{K+4-a}\) have period \(54\), while the linear factors in \(K\) have period \(81\). Thus \(T\bmod81\), and hence \(X\bmod27\), is determined by \(K\bmod162\) and \(a\bmod54\).

For a fixed \(a\bmod54\), define the two exceptional base residues
\[
K_0\equiv12-3a\pmod{54},\qquad
K_1\equiv48-3a\pmod{54}.
\]
For each \(i\in\{0,1\}\), the three lifts modulo \(162\) are represented by
\[
K_i,\quad K_i+54,\quad K_i+108.
\]
The table gives, in that order, \(X\bmod27\) in the \(K_0\) phase and the forced first-parent height \(h\bmod9\) in the \(K_1\) phase. Here
\[
h=2(X/3)-4p-K-4,\qquad p=2^K.
\]

| \(a\bmod54\) | \(K_0\) | \(X\bmod27\) on its three lifts | \(m_0\) | \(K_1\) | \(h\bmod9\) on its three lifts | \(m_1\) |
|---:|---:|:---:|---:|---:|:---:|---:|
| 1  | 9  | (18, 9, 0) | 2 | 45 | (2, 5, 8) | 0 |
| 3  | 3  | (0, 18, 9) | 0 | 39 | (2, 5, 8) | 0 |
| 5  | 51 | (0, 18, 9) | 0 | 33 | (2, 5, 8) | 0 |
| 7  | 45 | (0, 18, 9) | 0 | 27 | (5, 8, 2) | 2 |
| 9  | 39 | (9, 0, 18) | 1 | 21 | (5, 8, 2) | 2 |
| 11 | 33 | (18, 9, 0) | 2 | 15 | (5, 8, 2) | 2 |
| 13 | 27 | (18, 9, 0) | 2 | 9  | (8, 2, 5) | 1 |
| 15 | 21 | (0, 18, 9) | 0 | 3  | (8, 2, 5) | 1 |
| 17 | 15 | (9, 0, 18) | 1 | 51 | (2, 5, 8) | 0 |
| 19 | 9  | (9, 0, 18) | 1 | 45 | (5, 8, 2) | 2 |
| 21 | 3  | (18, 9, 0) | 2 | 39 | (5, 8, 2) | 2 |
| 23 | 51 | (18, 9, 0) | 2 | 33 | (5, 8, 2) | 2 |
| 25 | 45 | (18, 9, 0) | 2 | 27 | (8, 2, 5) | 1 |
| 27 | 39 | (0, 18, 9) | 0 | 21 | (8, 2, 5) | 1 |
| 29 | 33 | (9, 0, 18) | 1 | 15 | (8, 2, 5) | 1 |
| 31 | 27 | (9, 0, 18) | 1 | 9  | (2, 5, 8) | 0 |
| 33 | 21 | (18, 9, 0) | 2 | 3  | (2, 5, 8) | 0 |
| 35 | 15 | (0, 18, 9) | 0 | 51 | (5, 8, 2) | 2 |
| 37 | 9  | (0, 18, 9) | 0 | 45 | (8, 2, 5) | 1 |
| 39 | 3  | (9, 0, 18) | 1 | 39 | (8, 2, 5) | 1 |
| 41 | 51 | (9, 0, 18) | 1 | 33 | (8, 2, 5) | 1 |
| 43 | 45 | (9, 0, 18) | 1 | 27 | (2, 5, 8) | 0 |
| 45 | 39 | (18, 9, 0) | 2 | 21 | (2, 5, 8) | 0 |
| 47 | 33 | (0, 18, 9) | 0 | 15 | (2, 5, 8) | 0 |
| 49 | 27 | (0, 18, 9) | 0 | 9  | (5, 8, 2) | 2 |
| 51 | 21 | (9, 0, 18) | 1 | 3  | (5, 8, 2) | 2 |
| 53 | 15 | (18, 9, 0) | 2 | 51 | (8, 2, 5) | 1 |

The table has two uniform consequences:
- In every \(K_0\) row, the three values of \(X\bmod27\) are a permutation of \(0,9,18\). The unique lift with value \(0\) has \(27\mid X\); the other two have \(v_3(X)=2\).
- In every \(K_1\) row, the three values of \(h\bmod9\) are a permutation of \(2,5,8\). The unique lift with value \(2\) has \(9\mid2h+5\); the other two have \(v_3(2h+5)=1\).

The column \(m_0\) is the unique lift index with \(X\equiv0\pmod{27}\), and \(m_1\) is the unique lift index with \(h\equiv2\pmod9\). Hence the two unresolved classes are explicitly
\[
K\equiv K_0+54m_0(a)\pmod{162},\qquad
K\equiv K_1+54m_1(a)\pmod{162}.
\tag{4}
\]

## 2. The two non-high lifts in the X ≡ 0 phase are parentless

In the \(K_0\) phase, the two non-high lifts have \(X\bmod27=9\) or \(18\), so \(v_3(X)=2\). The odd ResetParent equation forces \(t=1\), with odd parameter \(d=X/9\). Its source-band parameter is \(2d\), and
\[
\frac{2d}{p}
=\frac{160-64x+(4K+26)/p}{27}.
\tag{5}
\]
For \(x\in\mathcal W\subset[97/64,13/8]\) and \(K\ge266\),
\[
2<\frac{2d}{p}<\frac{64}{27}<3.
\tag{6}
\]
Every odd source band is \([6\cdot2^k+1,8\cdot2^k-1]\). For \(k\le K-2\) its upper endpoint is at most \(2p-1\); for \(k\ge K-1\) its lower endpoint is at least \(3p+1\). Thus \(2d\in(2p,3p)\) lies in no odd source band. The previous theorem gives \(4p<E<6p-1\), so \(E\) has no even parent either. These two lifts are root-excluded. The unique remaining lift has \(27\mid X\), so \(t\ge2\) may still occur.

## 3. The two non-high lifts in the X ≡ 3 phase are parentless

In the \(K_1\) phase, the first odd parent of \(E\) is
\[
h=2(X/3)-4p-K-4.
\]
For the two lifts with \(h\equiv5\) or \(8\pmod9\),
\[
Y=2h+5\equiv6\ \text{or}\ 3\pmod9,
\]
so \(v_3(Y)=1\). The only possible odd-parent parameter of \(h\) is \(g=Y/3\). The exact normalized expressions are
\[
\frac gp=\frac{248-128x}{27}+\frac{25-10K}{27p},
\qquad
G=2g-2p-K-3,
\]
and
\[
\frac Gp=\frac{442-256x}{27}-\frac{47K+31}{27p}.
\]
For \(x\in\mathcal W\), the bounds in the preceding derivation give
\[
\frac32<\frac gp<2,\qquad p<G<\frac{3p}{2}.
\]
Thus \(g\) is in the unique odd source band at scale \(K-2\), but its parent \(G\) lies in the even gap between the scale-\((K-3)\) and scale-\((K-2)\) bands. Also \(G\equiv0\) or \(1\pmod3\), so it has no odd parent. Hence \(G\) is parentless, then \(h\), then \(E\). These two lifts are root-excluded. The unique remaining lift has \(h\equiv2\pmod9\), so \(9\mid2h+5\) and a higher valuation remains possible.

## 4. Combined count and exact scope

There are nine allowed residues modulo \(54\), each with three lifts modulo \(162\), for 27 classes total. The first theorem excludes all three lifts of seven phases (21 classes). The table and gap arguments exclude two lifts in each of the remaining two phases (four more classes). Thus 25 of 27 classes are excluded, leaving exactly the two high-valuation classes in (4).

The result does not decide those two classes: one has \(27\mid X\), the other \(9\mid2h+5\). Nor does it exclude other odd branches leaving earlier spine nodes or prove the fatal target unreachable. The accompanying t0_odd_a_k3_second_lift.mjs checks the exact 27-row modular table; the inequalities and parent-chain proofs are separate exact arguments.
