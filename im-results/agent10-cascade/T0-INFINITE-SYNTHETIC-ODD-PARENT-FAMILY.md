# Infinite t=0 fatal family excluded by a unique odd-parent leaf

**Status:** the conditional rho=38 root-exclusion theorem is now formalized in [T0Rho38RootExclusion.lean](T0Rho38RootExclusion.lean), importing the source-certified \`ResetParent\` and \`ResetChain\` definitions. Manual original-source CI run [44203014937](https://github.com/FlareZ123/bb6/actions/runs/44203014937) is pending. The existence of infinitely many parameter pairs and the t=0 fatal-source interpretation below remain paper derivations, so this dossier stays in \`im-results/\`. It is not a global nonhalting proof.

## Theorem

There are infinitely many t=0 adjacent-fatal source candidates \(E\) for which
\[
\neg\operatorname{ResetChain}(2,E).
\]
For every member of this family:

1. \(E\) has no even \(\operatorname{ResetParent}\).
2. \(E\) has exactly one odd \(\operatorname{ResetParent}\), namely \(h'\) at level \(L=K-1\).
3. \(h'\) has no \(\operatorname{ResetParent}\) of either parity.

Thus \(E\) is not reachable from the blank reset root. Its associated t=0 fatal tail cannot occur on the blank-root trajectory. This excludes an infinite subfamily of candidate fatal histories, not all possible halting histories of machine #746.

The initial interval was sharpened by Agent 7 to \([38/25,31/20]\); the argument below widens it further to \([97/64,13/8]\). The proof uses the exact two-arm \(\operatorname{ResetParent}\) definition in [FirstInverseComplete.lean](FirstInverseComplete.lean) and the root-chain equivalence in [ResetChain.lean](ResetChain.lean). It does **not** rely on the still-uncompiled t=0 even-parent branch draft.

## Infinite parameter family and fatal source

Take
\[
a=18n\quad(n\ge1),\qquad K\equiv38\pmod{54},
\qquad
\frac{97}{64}\le x:=\frac{2K+7}{2^a}\le\frac{13}{8}.
\tag{1}
\]
For each \(a=18n\), the eligible \(K\)-interval has length \(7\cdot2^a/128>54\), so it contains an integer in the residue class \(38\bmod54\). Hence infinitely many pairs \((a,K)\) exist. They all have \(K\ge266\).

Put
\[
p=2^K,\quad c=2K+7,\quad r=K+1-a,\quad B_0=c\,2^{r+3},
\]
and
\[
D_0=\frac{B_0-16p+2K+1}{3},\qquad E=8p+K-D_0.
\tag{2}
\]
Here \(K\equiv2\bmod6\), \(a\) is even, \(r\) is odd, and \(a=\lfloor\log_2 c\rfloor\). Also \(4c\le7\cdot2^a\), since \(x\le13/8<7/4\). The fatal-source equation is
\[
B_0=40p+K-1-3E.
\tag{3}
\]
The numerator defining \(D_0\) is divisible by \(3\): modulo \(3\), \(c\equiv2\), \(2^{r+3}\equiv1\), \(16p\equiv1\), and \(2K+1\equiv2\).

Since \(B_0=16xp\), the interval in (1) puts \(B_0\) strictly inside
\[
16p+4K+20\le B_0\le28p+4K+8.
\]
Equivalently, the t=0 raw odd-source parameter
\[
d_0=4p+\frac{E+K+5}{2}
\]
satisfies \(6p+1\le d_0\le8p-1\). Equation (3), with \(16\mid B_0\), gives \(E+K\equiv1\bmod4\), so this is a genuine odd-exit source. The same interval gives
\[
4p-K-3\le E\le8p-K-7,
\]
which certifies \(\operatorname{FirstFailureAt}(E,K)\).

Moreover, (3) is exactly the t=0 adjacent-fatal identity:
\[
3d_0+\frac{B_0}{2}=32p+2K+7,
\qquad
\frac{B_0}{2}=2^{r+1}(4K+14).
\tag{4}
\]
Thus \(E\) is a t=0 fatal-source candidate: its odd child has the prescribed same-level even deficit \(2^r(4K+14)\), followed by the fatal even exit.

## Exact odd parent of E

The residues are
\[
2^a\equiv1\pmod{27},\quad
K\equiv11\pmod{27},\quad
K+4-a\equiv6\pmod{18},\quad
2^{K+4-a}\equiv10\pmod{27}.
\]
Using
\[
3D_0=(c-2^a)2^{K+4-a}+2K+1,
\]
we obtain
\[
3D_0\equiv(2-1)\cdot10+23\equiv6\pmod{27},
\]
hence \(D_0\equiv2\bmod9\). Also
\[
A:=16p+2K+5\equiv1\pmod9,\qquad
X:=2E+5=A-2D_0\equiv6\pmod9.
\tag{5}
\]
Therefore \(v_3(X)=1\) exactly. Set
\[
P=X/3.
\]
Then \(P\) is odd. Direct substitution gives
\[
\frac{P}{p}
=\frac{80-32x+(2K+13)/p}{9}.
\tag{6}
\]
For \(97/64\le x\le13/8\) and \(K\ge266\), this lies strictly between \(3\) and \(4\): the lower bound is \(28/9>3\), while the upper bound is at most \(7/2+1/9=65/18<4\). Thus, with \(L=K-1\),
\[
6\cdot2^L+1\le P\le8\cdot2^L-1.
\tag{7}
\]
Define
\[
h'=2P-8\cdot2^L-L-5.
\tag{8}
\]
Then
\[
2P=8\cdot2^L+h'+L+5,\qquad 2E+5=3P.
\]
Together with (7), these are exactly the odd arm of \(\operatorname{ResetParent}(h',E)\), with \(t=0\).

This odd parent is unique. Any odd parent of \(E\) has
\[
2E+5=3^{t+1}d.
\]
By (5), \(v_3(2E+5)=1\), so \(t=0\) and \(d=P\). The odd source bands \([6\cdot2^j+1,8\cdot2^j-1]\) are pairwise disjoint, and (7) places \(P\) in the unique band \(j=L\). The source equation then forces the parent height to be exactly \(h'\).

## E has no even parent

From (2),
\[
\frac{E}{p}
=8-\frac{16}{3}(x-1)+\frac{K-1}{3p}.
\]
The interval (1), together with \(K-1<p/4\), gives
\[
\frac{14}{3}<\frac{E}{p}
<\frac{21}{4}+\frac1{12}
=\frac{16}{3}<6.
\tag{9}
\]
An even parent at level \(j\) would require
\[
6\cdot2^j-1\le E\le8\cdot2^j-3.
\]
For \(j\le K-1\), the upper bound is at most \(4p-3<E\). For \(j\ge K\), the lower bound is at least \(6p-1>E\), by (9) and \(16p/3<6p-1\). Hence \(E\) has no even parent. Its unique parent of either parity is \(h'\).

## h' has no parent

First, (5) gives \(P\equiv2\bmod3\). Since \(L=K-1\equiv1\bmod6\),
\[
h'=2P-8\cdot2^L-L-5\equiv0\pmod3.
\tag{10}
\]
Every odd-parent output \(u\) satisfies \(2u+5=3^{t+1}d\), hence \(u\equiv2\bmod3\). Equation (10) therefore excludes every odd parent of \(h'\).

For even parents, (6) and (8) simplify to
\[
\frac{h'}p
=\frac{124-64x-(5K+10)/p}{9}.
\tag{11}
\]
For \(K\ge266\), \(5K+10<p\). Using (1) in (11),
\[
\frac{19}{9}
<
\frac{h'}p
<
3.
\]
More precisely, \(3p-h'\ge(5K+10)/9>1\), so \(2p<h'<3p-1\). An even parent at level \(j\le K-2\) has target at most \(2p-3<h'\). An even parent at level \(j\ge K-1\) has target at least \(3p-1>h'\). Thus \(h'\) has no even parent either.

Combining (10) and (11), \(h'\) has no \(\operatorname{ResetParent}\) at all.

## Lean formalization scope

`CascadeT0Rho38.entry_not_root` proves the conditional root exclusion for every pair satisfying `a % 18 = 0`, `K % 54 = 38`, `K >= 266`, `a <= K`, and the two integer inequalities equivalent to `97/64 <= (2K+7)/2^a <= 13/8`. The Lean proof derives the exact `X % 9 = 6` valuation, constructs the unique odd predecessor at level `K-1`, excludes even predecessors for both the candidate and that predecessor, and closes the root-chain contradiction through `root_reset_chain_iff`. It does not yet formalize the interval-pigeonhole argument producing such a `K` for every `a=18n`, nor the separate identification of `E` as the t=0 adjacent-fatal source. Those two links remain in the paper derivation above.

## Root nonreachability

The exact source theorem \(\operatorname{root\_reset\_chain\_iff}\) identifies blank-root reachability with finite \(\operatorname{ResetParent}\)-chains from \(2\). If \(E\) were root-reachable, its last predecessor would have to be its unique parent \(h'\). But \(h'\ne2\) and has no parent, so no such chain can exist:
\[
\neg\operatorname{ResetChain}(2,E).
\]
Therefore the t=0 fatal-source configuration \(E\), and its associated fatal tail, are excluded from the blank-root trajectory for every pair in (1).

This is an infinite, root-specific exclusion theorem for one structured family. It does not decide the other t=0 phases, the t=1 or higher-valuation branches, or the global nonhalting question.

## Related finite exclusion

Agent 7's separate \(K=1023,q=8\) t=0 candidate has a unique seven-edge reverse-parent chain ending at a parentless source. See [the K=1023 note](../agent7-746-even-parent/K1023-T0-ENTRY-ROOT-EXCLUSION.md) and [its exact reproducer](../agent7-746-even-parent/k1023_t0_root_exclusion.mjs). This is a distinct candidate and not part of the infinite family above.

## Reproducible instance

The accompanying BigInt script checks
\[
a=18,\quad K=202538,\quad r=202521,\quad L=202537.
\]
It verifies the exact divisibilities, source bands, the unique odd parent, the mod-3 parentless condition, both dyadic gaps excluding even parents, and all displayed first-failure endpoint inequalities.

Run:
\`\`\`bash
node im-results/agent10-cascade/t0_infinite_synthetic_odd_parent_family.mjs
\`\`\`
