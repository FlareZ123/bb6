# Eight-of-nine t=0 fatal-source phase classes are outside the blank-root chain

**Status:** exact paper-level arithmetic over the repository's original-source ResetParent grammar; the modular and interval derivation has not yet been formalized in Lean. The eight non-rho-20 phases remain root-leaf exclusions. The later rho-20 lift-cascade claim of 80/81 exclusions is withdrawn: every rho-20 candidate has an omitted t=0 parent at level K-1. A separate paper-level theorem now excludes the infinite subfamily a≡0 (mod 54), K=97·2^(a-7)+30, by showing its complete inverse-parent graph is a unique chain ending in a non-root leaf. Other rho-20 parameters remain open. The corrected parent fan and proof are in [T0-RHO20-TWO-OF-THREE-LIFTS.md](T0-RHO20-TWO-OF-THREE-LIFTS.md).

## Theorem

Let \(a\ge10\) be even, \(K\ge266\), and put
\[
p=2^K,\qquad c=2K+7,\qquad
x=\frac{c}{2^a},\qquad r=K+1-a.
\]
Assume
\[
K\equiv2\pmod6,\qquad
\frac{97}{64}\le x\le\frac{13}{8},\qquad
\rho:=K+6a\not\equiv20\pmod{54}.
\tag{1}
\]
Then \(a=\lfloor\log_2 c\rfloor\), \(r\) is odd, and the exact t=0 adjacent-fatal source candidate \(E\) defined below is not in the genuine blank-root reset chain:
\[
\neg\operatorname{ResetChain}(2,E).
\]

For each fixed even \(a\ge10\), the interval for \(K\) has width
\[
\frac{7\cdot2^a}{128}>54.
\]
Consequently it contains a representative of every residue class \(K\bmod54\) compatible with \(K\equiv2\bmod6\). Exactly one of the nine corresponding phases has \(\rho=20\); the other eight all satisfy (1). Thus this gives infinitely many root-unreachable t=0 candidates, in eight of the nine modular phases for every sufficiently large even \(a\).

The phase count is a statement about these parameter residue classes only. It is not a density statement about machines, halting histories, or the BB(6) search space.

## Exact t=0 candidate

Set
\[
B=c\,2^{r+3}=c\,2^{K+4-a},\qquad
3D=B-16p+2K+1,\qquad
E=8p+K-D.
\tag{2}
\]
The numerator defining \(D\) is divisible by \(3\). Indeed, \(K\) and \(a\) are even, \(K\equiv2\pmod3\), and \(2^{K+4-a}\equiv2^a\equiv1\pmod3\). The explicit t=0 source criterion in [Agent 7's fatal-depth derivation](../agent7-746-even-parent/T0-FATAL-DEPTH-EXPLICIT-R.md) applies: \(r=K+1-a\) is odd and \(4c\le7\cdot2^a\), since \(x\le13/8<7/4\).

The defining equation gives
\[
B=40p+K-1-3E.
\tag{3}
\]
Moreover,
\[
\frac Dp=\frac{16}{3}(x-1)+\frac{2K+1}{3p},
\qquad
\frac Ep=\frac{40-16x}{3}+\frac{K-1}{3p}.
\tag{4}
\]
For \(K\ge266\), the interval in (1) implies
\[
\frac{14}{3}<\frac Ep<\frac{16}{3}.
\tag{5}
\]
In particular,
\[
4p<E<6p-1.
\tag{6}
\]
Since \(2p>K+7\), these bounds also put \(E\) inside the exact first-failure interval \(4p-K-3\le E\le8p-K-7\).

The raw odd-source parameter for this t=0 candidate is
\[
d_0=4p+\frac{E+K+5}{2}.
\]
Since \(r+3=K+4-a\) is even, \(16\mid B\). Equation (3) then gives \(E+K\equiv1\pmod4\), so \(d_0\) is an odd integer. From (5), \(K+5<p\), and \(p=2^K\),
\[
\frac{19}{3}p<d_0<
4p+\frac{16p/3+p}{2}
=\frac{43}{6}p<8p.
\]
Hence \(6p+1\le d_0\le8p-1\). Finally,
\[
3d_0+\frac B2=32p+2K+7,\qquad
\frac B2=(2K+7)2^{r+2},
\]
which is the exact t=0 adjacent-fatal source identity. Thus (2) defines a genuine member of the t=0 fatal-source candidate family, rather than an arbitrary inverse target.

## The modular phase collapse

Write
\[
X=2E+5=16p+2K+5-2D.
\tag{7}
\]
From (2),
\[
3D=(2K+7-2^a)2^{K+4-a}+2K+1.
\tag{8}
\]
Because powers of \(2\) have period \(18\) modulo \(27\), substituting the nine even residues \(a\bmod18\) and the nine possible values of \(\rho=K+6a\bmod54\) gives the following exact table. Each set lists the values of \(X\bmod9\) as \(a\bmod18\) ranges over \(0,2,\ldots,16\).

| \(\rho\bmod54\) | Possible values of \(X\bmod9\) |
|---:|:---|
| 2 | \(\{3\}\) |
| 8 | \(\{2,5,8\}\) |
| 14 | \(\{1,4,7\}\) |
| 20 | \(\{0\}\) |
| 26 | \(\{2,5,8\}\) |
| 32 | \(\{1,4,7\}\) |
| 38 | \(\{6\}\) |
| 44 | \(\{2,5,8\}\) |
| 50 | \(\{1,4,7\}\) |

In particular, \(X\not\equiv0\pmod9\) for every phase except \(\rho=20\). There are two cases.

### Case 1: \(3\nmid X\)

Every odd ResetParent of \(E\) would require \(3\mid2E+5=X\), by the odd arm of ResetParent in [FirstInverseComplete.lean](FirstInverseComplete.lean). So \(E\) has no odd parent. Equation (6) places it strictly between all even-parent target bands: an even parent at level \(j\le K-1\) has target at most \(4p-3<E\), while one at level \(j\ge K\) has target at least \(6p-1>E\). Hence \(E\) itself is parentless.

### Case 2: \(X\equiv3\) or \(6\pmod9\)

Now \(v_3(X)=1\), so every odd parent must have valuation \(t=0\) and odd parameter
\[
d=\frac X3.
\]
Using (4) and (7),
\[
\frac dp=\frac{80-32x+(2K+13)/p}{9}.
\]
The interval (1) and \(K\ge266\) give
\[
3p<d<4p.
\]
Thus \(d\) belongs to exactly one odd-source band, namely the level \(K-1\) band \([3p+1,4p-1]\). The odd parent is therefore unique and equals
\[
h=2d-4p-K-4.
\tag{9}
\]
Its normalized height is
\[
\frac hp=\frac{124-64x-(5K+10)/p}{9}.
\]
The endpoint bounds in (1), together with \(2p>5K+10\), give \(2p<h\). Also
\[
3p-h=\frac{(64x-97)p+5K+10}{9}>1,
\]
so the integer \(h\) satisfies
\[
2p<h<3p-1.
\tag{10}
\]
Consequently \(h\) lies between all even-parent target bands: levels \(j\le K-2\) end at most at \(2p-3\), and levels \(j\ge K-1\) start at least at \(3p-1\).

It remains to exclude odd parents of \(h\). Since \(K\equiv2\pmod6\), \(p\equiv1\pmod3\) and \(K\equiv2\pmod3\). If \(X\equiv3\pmod9\), then \(d\equiv1\pmod3\), so (9) gives \(h\equiv1\pmod3\). If \(X\equiv6\pmod9\), then \(d\equiv2\pmod3\), so (9) gives \(h\equiv0\pmod3\). Every odd-parent target \(u\) must satisfy \(2u+5\equiv0\pmod3\), hence \(u\equiv2\pmod3\). In either subcase \(h\) has no odd parent. Together with (10), this proves that \(h\) is parentless.

Thus, in Case 2, \(E\) has exactly one parent \(h\), and that parent has no parent. In Case 1, \(E\) has no parent at all.

## Blank-root conclusion and exact scope

The already source-certified theorem root_reset_chain_iff in [ResetChain.lean](ResetChain.lean) identifies genuine blank-root reset reachability with finite ResetParent chains from \(2\). A parentless \(E\), or a target \(E\) whose unique parent is a parentless \(h\ne2\), cannot lie on such a chain. Therefore every candidate satisfying (1) is excluded from the genuine blank-root trajectory.

This is stronger than the two earlier t=0 q=0 subfamilies:
- [The unique-odd-parent leaf family](T0-INFINITE-SYNTHETIC-ODD-PARENT-FAMILY.md) is the special phase \(\rho=38\), \(a\equiv0\pmod{18}\).
- [The \(D_0\equiv0\pmod3\) family](T0-D0-ZERO-PHASE-ROOT-EXCLUSION.md) lies among the phases with \(3\nmid X\).

The old notes remain useful worked derivations and are not deleted. Agent 7's separate \(K=1023,q=8\) seven-edge chain is a different candidate with nonzero same-level reset depth; it is not part of this q=0 family.

The rho-20 phase is not fully resolved. The infinite subfamily a≡0 mod54, K=97*2^(a-7)+30 is excluded by a unique complete inverse-parent chain ending in a non-root leaf. The other rho-20 parameter classes, K≡3 mod6 sector, nonzero same-level reset depths, higher fatal branches, and all other root families remain open. This result does not prove that #746 is nonhalting and does not determine BB(6).

## Reproducer

Run the Node.js script [t0_eight_of_nine_phase_root_exclusion.mjs](t0_eight_of_nine_phase_root_exclusion.mjs). It checks the full \(9\times9\) modular table and exact BigInt witnesses for all nine phases at \(a=10\). The script is a finite arithmetic regression, not a substitute for the infinite inequalities above or for a Lean proof.
