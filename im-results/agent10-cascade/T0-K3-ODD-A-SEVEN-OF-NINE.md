# Odd-a, K ≡ 3 (mod 6): seven of nine t=0 phases are root-excluded

**Status:** new paper-level arithmetic reduction, derived against the exact two-arm ResetParent grammar. The modular table is independently reproducible; the infinite inequalities and source-spine composition have not yet been Lean-formalized or independently reviewed. Keep this in im-results. This excludes one auxiliary t=0 branch, not the fatal target or all possible root paths.

## Theorem

Let \(a\ge 11\) be odd and \(K\ge266\) satisfy
\[
K\equiv3\pmod6,\qquad
\frac{97}{64}\le x:=\frac{2K+7}{2^a}\le\frac{13}{8}.
\tag{1}
\]
Put
\[
p=2^K,\quad c=2K+7,\quad r=K+1-a,\quad
B=c\,2^{K+4-a},
\]
and define
\[
D=\frac{B+2K+1-16p}{3},\qquad E=8p+K-D.
\tag{2}
\]
The numerator defining \(D\) is divisible by three. Then \(E\) is a genuine t=0 odd-parent predecessor on the canonical fatal-target spine described below, and
\[
\neg\operatorname{ResetChain}(2,E)
\]
whenever
\[
K\not\equiv 12-3a,\ 48-3a\pmod{54}.
\tag{3}
\]

For every fixed odd \(a\ge11\), the interval (1), viewed as an interval for \(K\), has width
\[
\frac{7\cdot2^a}{128}>54.
\]
It therefore contains an integer in every one of the nine residue classes
\[
K\equiv3,9,15,21,27,33,39,45,51\pmod{54}.
\]
Exactly two of those nine classes are left open by (3). Thus seven of nine t=0 candidate phases are excluded for every such \(a\).

## 1. The candidate is an actual branch of the fatal-target spine

Write \(n=K+2\) and let
\[
F_n=4\cdot2^n-n-4=16p-K-6.
\]
For each \(j\ge0\), define the canonical ray
\[
u_j=16p-c\,2^j+K+1,\qquad J=K+2-a.
\]
Then \(u_0=F_n\), and
\[
2u_j=16p+u_{j+1}+K+1.
\]
This is precisely the even ResetParent equation at scale \(K+1\). Consequently the ray segment from \(F_n\) to \(u_J\) consists of \(J\) genuine even-parent edges.

Since \(c2^J=B/4\),
\[
2u_J+5=32p-\frac B2+c.
\]
Set
\[
d_0=\frac{2u_J+5}{3}.
\]
The definitions (2) give the exact identities
\[
3d_0+\frac B2=32p+2K+7,\qquad
2d_0=8p+E+K+5.
\tag{4}
\]
Thus \(E\) is the t=0 odd ResetParent of \(u_J\), at scale \(K\), provided \(d_0\) is in its required odd source band.

The source-band conditions hold. Indeed, \(K\equiv3\pmod6\) and odd \(a\) imply that \(r\) is odd and \(K+4-a\) is even. Hence \(16\mid B\). Also \(c/2^a=x\in(1,2)\), so \(a=\lfloor\log_2 c\rfloor\), and \(x\le13/8<7/4\) gives the required t=0 source-depth guard.

Modulo three, \(K\equiv0\), \(p=2^K\equiv2\), \(c\equiv1\), and \(2^{K+4-a}\equiv1\). Therefore
\[
B+2K+1-16p\equiv1+1-2\equiv0\pmod3.
\]
So \(D\) is an integer and
\[
E=\frac{40p+K-1-B}{3}.
\tag{5}
\]
Since \(B\equiv0\pmod{16}\), \(40p\equiv0\pmod{16}\), and \(K-1\) is even, (5) implies \(E\) is even. Reducing (5) modulo four gives
\[
E+K+5\equiv2\pmod4.
\]
Thus \(d_0=4p+(E+K+5)/2\) is an odd integer.

The normalized height is
\[
\frac Ep=\frac{40-16x}{3}+\frac{K-1}{3p}.
\]
For \(K\ge266\), (1) and \(4(K-1)<p\) give
\[
\frac{14}{3}<\frac Ep<\frac{16}{3},
\qquad
\frac{19}{3}<\frac{d_0}{p}<\frac{43}{6}.
\]
In particular,
\[
4p<E<6p-1,\qquad 6p+1\le d_0\le8p-1.
\tag{6}
\]
This proves the exact source-band condition in (4). It also shows that \(E\) has no even ResetParent: an even target band at scale \(j\) is
\[
[6\cdot2^j-1,\ 8\cdot2^j-3],
\]
whose adjacent bands around this interval end at \(4p-3\) and begin at \(6p-1\).

## 2. Exact modulo-nine phase table

Let \(X=2E+5\). From (5),
\[
X=\frac{80p+2K+13-2(2K+7)2^{K+4-a}}{3}.
\tag{7}
\]
The numerator is divisible by three. Since \(2\) has order \(18\) modulo \(27\), the residue \(X\bmod9\) is determined entirely by \(a\bmod18\) and \(K\bmod54\).

The complete table is:

| \(a\bmod18\) \ \(K\bmod54\) | 3 | 9 | 15 | 21 | 27 | 33 | 39 | 45 | 51 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1  | 7 | 0 | 2 | 4 | 6 | 8 | 1 | 3 | 5 |
| 3  | 0 | 8 | 7 | 6 | 5 | 4 | 3 | 2 | 1 |
| 5  | 5 | 1 | 6 | 2 | 7 | 3 | 8 | 4 | 0 |
| 7  | 4 | 6 | 8 | 1 | 3 | 5 | 7 | 0 | 2 |
| 9  | 6 | 5 | 4 | 3 | 2 | 1 | 0 | 8 | 7 |
| 11 | 2 | 7 | 3 | 8 | 4 | 0 | 5 | 1 | 6 |
| 13 | 1 | 3 | 5 | 7 | 0 | 2 | 4 | 6 | 8 |
| 15 | 3 | 2 | 1 | 0 | 8 | 7 | 6 | 5 | 4 |
| 17 | 8 | 4 | 0 | 5 | 1 | 6 | 2 | 7 | 3 |

Each row is a permutation of \(0,\ldots,8\). More specifically, for each odd \(a\bmod18\), the three exceptional columns are exactly
\[
\begin{array}{c|c}
X\bmod9 & K\bmod54\\ \hline
0 & 12-3a\\
3 & 48-3a\\
6 & 30-3a.
\end{array}
\tag{8}
\]
The other six columns give \(X\bmod9\in\{1,2,4,5,7,8\}\).

## 3. Root exclusion in seven phases

If \(X\not\equiv0\pmod3\), then \(E\) has no odd ResetParent, because every odd parent in the exact grammar requires \(3\mid 2E+5\). Together with (6), \(E\) is parentless.

It remains to handle the \(X\equiv6\pmod9\) phase, namely
\[
K\equiv30-3a\pmod{54}.
\]
Here \(v_3(X)=1\). Put \(d=X/3\), which is odd because \(E\) is even. Equation (7) gives
\[
\frac dp=\frac{80-32x+(2K+13)/p}{9}.
\]
Using (1) and \(2K+13<p\),
\[
\frac{28}{9}<\frac dp<\frac{65}{18}<4.
\]
Hence \(3p<d<4p\), so the odd parameter \(d\) lies in exactly one odd source band, at scale \(K-1\):
\[
6\cdot2^{K-1}+1\le d\le8\cdot2^{K-1}-1.
\]
The odd-parent equation therefore forces the unique parent
\[
h=2d-4p-K-4.
\tag{9}
\]

Its normalized height is
\[
\frac hp=\frac{124-64x-(5K+10)/p}{9}.
\]
The bounds (1) and \(5K+10<p\) imply
\[
2p<h<3p-1.
\tag{10}
\]
Thus \(h\) lies in the even-parent gap between the scale-\((K-2)\) band, ending at \(2p-3\), and the scale-\((K-1)\) band, beginning at \(3p-1\).

Finally, \(K\equiv0\pmod3\) and \(p\equiv2\pmod3\). In the \(X\equiv6\pmod9\) phase, \(d\equiv2\pmod3\), so (9) gives
\[
h\equiv2d-4p-K-4\equiv1\pmod3.
\]
Every odd ResetParent target must be \(2\bmod3\). Therefore \(h\) has no odd parent either. Equations (10) and the residue calculation show that \(h\) has no parent of either parity.

Consequently:
- for the six phases \(X\bmod9\in\{1,2,4,5,7,8\}\), \(E\) is parentless;
- for the phase \(X\bmod9=6\), \(E\) has exactly one parent \(h\), and \(h\) is parentless.

The root-chain equivalence for the exact source grammar therefore gives
\[
\neg\operatorname{ResetChain}(2,E)
\]
in all seven phases.

## 4. Exact residual classes and scope

The only phases not covered by this argument are
\[
K\equiv12-3a\pmod{54}
\quad\text{and}\quad
K\equiv48-3a\pmod{54}.
\]
The first has \(9\mid X\), so higher odd valuations remain possible. The second has \(X\equiv3\pmod9\): its unique first odd parent has residue \(2\bmod3\), so the parentless argument above does not apply.

This is a seven-of-nine exclusion for the t=0 auxiliary branch in the \(K\equiv3\pmod6\), odd-\(a\) sector. It is not a proof that the fatal target \(F_{K+2}\) is unreachable: other odd branches at earlier spine nodes, the high-valuation exceptional classes, and the terminal weak-margin ray indices remain to be handled. In particular, it does not decide #746 or BB(6).

## Reproducer and next proof obligations

The accompanying t0_odd_a_k3_phase_table.mjs computes (7) modulo \(27\) for all \(9\times9\) residue pairs, checks divisibility by three, verifies the table, and asserts the three exceptional congruence formulas (8). It is a finite modular regression; the interval estimates and the source-spine argument above are separate exact derivations.

The next useful attack is the two residual classes in (8), especially the \(X\equiv3\pmod9\) class. For that class the first odd parent is forced, and its next parent problem can be studied using the exact dyadic source bands. The \(X\equiv0\pmod9\) class requires the higher 3-adic selector.
