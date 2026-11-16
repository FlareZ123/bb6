# Root/Q-depth alignment: exact odd-part test

**Status:** exact algebraic alignment criterion, plus an exact finite 100,000-reset orbit audit. This does not prove an all-time nonalignment theorem, decide the #746 blank root, or determine BB(6). Keep in im-results/.

## 1. The missing identification is an exact parent equation

Use the source reset grammar in [FirstInverseComplete.lean](../agent10-cascade/FirstInverseComplete.lean). At first-failure level \(K\), a source height \(q\) has the level certificate

\[
4\cdot2^K\le q+K+4,\qquad q+K+5<8\cdot2^K.
\]

The \(t=1\) odd arm from \(q\) to \(u\) at source scale \(K\) is exactly

\[
d\text{ odd},\qquad
6\cdot2^K+1\le2d\le8\cdot2^K-1,
\]
\[
2u+5=9d,\qquad 4d=8\cdot2^K+q+K+5.
\tag{1}
\]

For a canonical ray target \(u=\operatorname{ray}(n,j)\), the signed coordinate is
\(Z_j(n)=\operatorname{signedZ}(n,j)=2u+5\). The Q numerator is

\[
Q_j(n)=8Z_j(n)-9(2^{n+2}+2n+1)
      =28\cdot2^n-2n+15-2^{j+4}(2n+3).
\tag{2}
\]

The source-coordinate identity in Agent 44's [QStateIndexHensel.lean branch](https://github.com/FlareZ123/bb6/tree/agent44/q-state-index-hensel-20261113) proves that (1), with \(K=n-2\), implies

\[
Q_j(n)=9(2q+5).
\tag{3}
\]

There is also a useful converse. Assume \(q\) has the first-failure certificate at \(K=n-2\), \(n\ge4\), and (3) holds. From (2) and (3),

\[
8Z_j(n)=9(2^{n+2}+2n+2q+6).
\]

Since \(8\) and \(9\) are coprime, the integer
\[
d=\frac{2^{n+2}+2n+2q+6}{8}
\]
is well-defined and \(Z_j(n)=9d\). Rearranging gives
\[
4d=8\cdot2^{n-2}+q+(n-2)+5.
\]
The first-failure inequalities then imply the band in (1): the lower bound gives
\(4d\ge12\cdot2^{n-2}+1\), hence \(2d\ge6\cdot2^{n-2}+2\); the upper bound gives
\(4d\le16\cdot2^{n-2}-1\), hence \(2d\le8\cdot2^{n-2}-2\).
Also \(Z_j(n)\) is odd, so \(d\) is odd. Thus (3) is an exact characterization of a \(t=1\) source parent of the ray, once the source-level certificate is supplied.

**Important scale distinction:** the source parent scale is \(n-2\). If \(q\) is an actual root source height at first-failure level \(K\), uniqueness of that level forces \(n=K+2\). This identifies the index \(n\), not the ray depth \(j\).

## 2. The exact dyadic offset test determines \(j\)

Substituting \(n=K+2\) into (2) and imposing (3) gives

\[
\boxed{
B(K,q):=112\cdot2^K-2K-34-18q
       =(2K+7)2^{j+4}.
}
\tag{4}
\]

For the level deficit \(D=8\cdot2^K+K-q\), this is

\[
\boxed{
18D-32\cdot2^K-20K-34=(2K+7)2^{j+4}.
}
\tag{5}
\]

Consequently, there is at most one possible \(j\). It exists exactly when \(B>0\) and the odd part of \(B\) is \(2K+7\). In valuation notation,

\[
j=v_2(B)-4,\qquad
\frac{B}{2^{v_2(B)}}=2K+7.
\tag{6}
\]

For \(n\bmod6\in\{4,5\}\), the Q-depth base theorem forces this \(j\) to be even because (3) makes \(Q_j(n)\) divisible by three. Thus the actual condition is an exact odd-part match, not a guessed formula such as \(j=K\) or \(j=K-1\).

There is a particularly simple form when the source's own odd-exit offset is \(A=2a\), \(a\) odd. Since \(D=2A+2K+5=4a+2K+5\), equation (5) reduces to

\[
\boxed{
9a+2K+7-2^{K+2}=(2K+7)2^{j+1}.
}
\tag{7}
\]

This is the requested dyadic-band/offset test. The root's 3-adic height coverage is a separate filter: if the incoming root step gives
\(2q+5=3^{t_{\rm in}+1}d_{\rm in}\), then (3) gives
\(Q_j(K+2)=3^{t_{\rm in}+3}d_{\rm in}\). Hence, whenever the Q-depth selector hypotheses hold,

\[
j\bmod(2\cdot3^{t_{\rm in}+2})
=\operatorname{qDepthResidue}(K+2,t_{\rm in}+2).
\]

Additional factors of three in \(d_{\rm in}\) allow higher precision. This congruence is necessary but not sufficient; (4) or (7) is the exact binary match.

If the level entry undergoes same-level even resets before its odd exit, use the actual odd-exit source height
\(q=8\cdot2^K+K-D_{\rm exit}\), not the original entry height. The same criterion applies because the source scale remains \(K\).

## 3. Exact finite root-orbit audit

[root_qdepth_alignment.mjs](root_qdepth_alignment.mjs) implements the original first-reset recurrence with BigInt and tests (4) on every actual \(t=1\) odd reset edge. It also independently recomputes the first-failure level for the first 1,000 source and target states.

For 100,000 reset transitions from blank-root reset height \(2\), the exact run gives:

| Quantity | Count |
|---|---:|
| Completed reset transitions | 100,000 |
| Level entries, including root | 49,717 |
| Final first-failure level | 77,220 |
| Final height bit length | 77,223 |
| Maximum odd exponent encountered | 16 |
| Actual \(t=1\) odd source edges | 12,246 |
| Such edges with \(K+2\bmod6\in\{4,5\}\) | 4,078 |
| Positive \(B\) values | 1,726 |
| Cases with \(2K+7\mid B/8\) | 1 |
| Cases with \(B/[8(2K+7)]\) a power of two | **0** |
| Even-depth Q-parent alignments | **0** |

The final level, height bit length, and level-entry count agree with the existing independent 100,000-transition report in [ForwardOrbitAudit100k.md](../agent7-fatal-density/ForwardOrbitAudit100k.md).

The sole odd-factor-divisible candidate occurs at transition 188, \(K=152\), \(n=154\). Its quotient is

\[
\frac{B}{8(2K+7)}
=17249839203523543231215883055984150583733178
=2\cdot8624919601761771615607941527992075291866589,
\]
which is not a power of two. No exact alignment occurs in this prefix.

This audit covers all reset source states in the prefix, including intermediate same-level states, not just level-entry snapshots. It is still finite evidence and must not be promoted to a universal exclusion.

## 4. Consequence for the research direction

The Q-depth selector does not itself identify a blank-root parent. It parametrizes the 3-adic divisibility locus for each \(n\); the root supplies a particular source height \(q\); and the exact test (4) decides whether that height is the \(t=1\) parent of a ray at any even depth. The finite audit shows that broad 3-adic coverage does not make the binary offset match automatic.

The next useful theorem is a Lean iff combining qNumerator_t1_parent_identity with the first-failure source certificate and (4). After that, the genuine open problem is an all-time analysis of the odd-part equation along the deterministic root recurrence, or the discovery of its first actual solution. Do not infer a fixed relation between \(j\) and \(K\), and do not treat the 100,000-step exclusion as a proof for all time.


## 5. Updated research state — 16 November 2026

The source-level t=1 Q-parent/fatal-chain reduction has advanced in draft PR [#106](https://github.com/FlareZ123/bb6/pull/106), branch \`agent10/t1-q-fatal-source-20261116\`. Its \`T1QParentFatal.lean\` states the exact child-deficit identity, proves the required nonfatal even-reset chain, and gives \`root_t1_q_parent_fatal\`: any authentic blank-root t=1 Q-parent match reaches \(F_{K+2}\). The PR also derives \(j+2\le K\), the fatal-sector condition, and \(j\) even. **The PR is a draft and its source compile/axiom audit is still pending; do not cite it as verified.**

A further exact source-bound reduction is now available in [T1-Q-PARENT-FATAL-REDUCTION.md](T1-Q-PARENT-FATAL-REDUCTION.md): a genuine Q-aligned source \(q\) can occur only at the level entry or after one same-level even reset. Thus the actual root problem is reduced to at most two explicit entry-deficit candidates per \(K\), not a search over every same-level state.

Conversely, no uniform finite inverse-depth bound can be used to dispose of all synthetic Q candidates. [NESTED-ODD-PARENT-HENSEL.md](NESTED-ODD-PARENT-HENSEL.md) gives arbitrary finite-depth exact odd-parent chains on positive-density 3-adic cylinders in the fixed-depth \(j=3402\) family. This is not a root-reachability result: none of those chains is shown to contain root \(2\).

The exact 100,000-transition root audit remains finite evidence only. The remaining #746 obligation is to rule out (or exhibit) the actual root's entry-deficit equality with \(D_Q(K,j)\) or \(2D_Q(K,j)\) for all \(K\) in the surviving sectors, together with the other fatal branches. No all-time #746 verdict or BB(6) value follows.


## 6. Stronger root-entry phase restriction — 16 November 2026

For a genuine t=1 Q match at level \(K\ge10\), the level-entry state cannot be the result of an even exit from \(K-1\). The proof is in [T1-Q-PARENT-FATAL-REDUCTION.md](T1-Q-PARENT-FATAL-REDUCTION.md): an even-produced entry has deficit \(D_{\rm in}\in[4\cdot2^K+K,\ 4\cdot2^K+2K+1]\), whereas the Q equation plus \(m\le1\) makes this interval incompatible with the exact dyadic factor \(2^{j+4}\mid4\cdot2^K\) (or \(40\cdot2^K\)). Thus the entry must be an odd-reset output and is congruent to \(2\bmod3\).

The mod-27 phase refinement depends on \(j\bmod18\), not merely \(j\bmod6\). The corrected necessary pairs \((K\bmod18,j\bmod18)\) are listed in the T1 dossier separately for \(m=0\) and \(m=1\). The 14:00 K-only claim was explicitly retracted in Agent 7's 14:05 correction message. Do not use the withdrawn classification.

This removes the even-entry root phase for all \(K\ge10\), but leaves the odd-entry Hensel-compatible cases open. It is a mathematical derivation, not yet Lean-certified. No blank-root reachability or nonhalting conclusion follows.
