# Infinite q=0 t=0 root exclusion from the D0 ≡ 0 mod 3 phase

**Status:** exact paper derivation using the source-level \(\operatorname{ResetParent}\) inverse grammar. This new family arithmetic is not yet Lean-formalized. It is a partial exclusion, not a global nonhalting proof.

## Theorem

There are infinitely many t=0 fatal-source levels \(K\) for which the **q=0 first level-\(K\) entry** \(E\) has no \(\operatorname{ResetParent}\) of either parity. Consequently this q=0 fatal history is not in the blank-root reset chain.

This gives a second infinite q=0 root-exclusion family, independent of the unique-odd-parent-leaf family in [T0-INFINITE-SYNTHETIC-ODD-PARENT-FAMILY.md](T0-INFINITE-SYNTHETIC-ODD-PARENT-FAMILY.md). It instantiates the \(D_0\equiv0\bmod3\) phase identified in Agent 7's [3-adic selector](../agent7-746-even-parent/T0-ENTRY-ODD-PARENT-SELECTOR.md), but proves the even-parent obstruction directly from a dyadic gap rather than relying on the separate t=0 even-parent draft.

For \(q>0\), the same mod-3 calculation still excludes odd parents of the first entry, but the even-parent gap argument below is specific to \(q=0\); the separate even-parent theorem would be needed to finish those cases.

## Infinite parameter family and source entry

Take
\[
a=18n+2\quad(n\ge1),\qquad K\equiv2\pmod{18},
\qquad \frac32\le x:=\frac{2K+7}{2^a}\le\frac74.
\tag{1}
\]
For each \(a\), the eligible \(K\)-interval has length \(2^a/8>18\), so it contains an integer congruent to \(2\bmod18\). Hence infinitely many such \(K\) exist. They have \(K\ge266\).

Put
\[
p=2^K,\quad c=2K+7,\quad r=K+1-a,\quad B_0=c\,2^{r+3},
\]
and define
\[
D_0=\frac{B_0-16p+2K+1}{3},\qquad E=8p+K-D_0.
\tag{2}
\]
Here \(K\equiv2\bmod6\), \(a\equiv2\bmod6\), and \(r\equiv1\bmod6\), so \(r\) is odd. Also \(a=\lfloor\log_2c\rfloor\) and \(4c\le7\cdot2^a\). We are treating the q=0 case, so \(E\) is both the first level-\(K\) entry and the t=0 odd-exit source. Its fatal-source equation is
\[
B_0=40p+K-1-3E.
\tag{3}
\]
The numerator defining \(D_0\) is divisible by \(3\), as follows from the stronger modulo-\(9\) calculation below.

Since \(B_0=16xp\), (1) gives \(24p\le B_0\le28p\), which lies inside the t=0 source band
\[
16p+4K+20\le B_0\le28p+4K+8
\]
for \(K\ge266\). Thus the raw odd-source parameter
\[
d_0=4p+\frac{E+K+5}{2}
\]
is an odd integer in \([6p+1,8p-1]\), and
\[
4p-K-3\le E\le8p-K-7.
\]
In particular \(\operatorname{FirstFailureAt}(E,K)\) holds. Equation (3) is the q=0 t=0 adjacent-fatal source equation.

## The first entry has no odd parent

The exact deficit identity is
\[
3D_0=(c-2^a)2^{r+3}+2K+1.
\tag{4}
\]
From \(K\equiv2\bmod18\) and \(a\equiv2\bmod18\),
\[
c=2K+7\equiv2\pmod9,\qquad 2^a\equiv4\pmod9.
\]
Also \(r\equiv1\bmod6\), so \(2^{r+3}\equiv2^4\equiv7\bmod9\), and \(2K+1\equiv5\bmod9\). Therefore
\[
3D_0\equiv(2-4)\cdot7+5\equiv0\pmod9,
\]
hence
\[
D_0\equiv0\pmod3.
\tag{5}
\]
Since \(K\equiv2\bmod6\), \(A_K:=16p+2K+5\equiv1\bmod3\). For the q=0 first entry \(E=8p+K-D_0\),
\[
2E+5=A_K-2D_0\equiv1\pmod3.
\tag{6}
\]
Every odd-reset output \(u\) satisfies \(2u+5=3^{t+1}d\), so its left side is divisible by \(3\). Equation (6) excludes every odd parent of \(E\).

## The first entry has no even parent

Directly from (2) and (4),
\[
\frac{E}{p}
=8-\frac{16}{3}(x-1)+\frac{K-1}{3p}.
\tag{7}
\]
Using \(3/2\le x\le7/4\) and \(K-1<p/4\),
\[
4<\frac{E}{p}<\frac{16}{3}+\frac1{12}
=\frac{65}{12}<6.
\tag{8}
\]
In particular \(4p<E<6p-1\), since \(7p/12>1\).

An even parent at level \(j\) would require
\[
6\cdot2^j-1\le E\le8\cdot2^j-3.
\]
If \(j\le K-1\), its upper bound is at most \(4p-3<E\). If \(j\ge K\), its lower bound is at least \(6p-1>E\). Thus no even parent exists.

Combining (6) and (8), \(E\) has no \(\operatorname{ResetParent}\) at all.

## Root consequence

The root-chain equivalence in [ResetChain.lean](../ResetChain.lean) identifies blank-root reachability with finite \(\operatorname{ResetParent}\)-chains from \(2\). Since \(E>2\) and has no parent,
\[
\neg\operatorname{ResetChain}(2,E).
\]
The q=0 t=0 fatal source is \(E\) itself, so this q=0 fatal history is excluded from the blank-root trajectory for every \(K\) in (1).

This excludes one infinite q=0 phase family. Other \(K\bmod18,r\bmod6\) phases, q>0 cases, the remaining odd-parent cases, and higher-valuation branches remain open.

## Reproducible instance

The accompanying BigInt checker uses
\[
a=20,\quad K=786440,\quad r=786421.
\]
It verifies the parameter congruences, \(D_0\equiv0\bmod3\), the fatal source band, the first-failure endpoints, and the strict even-parent gap.

Run:
\`\`\`bash
node im-results/agent10-cascade/t0_d0_zero_phase_root_exclusion.mjs
\`\`\`
