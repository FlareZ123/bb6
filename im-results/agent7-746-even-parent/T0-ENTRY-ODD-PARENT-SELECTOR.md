# 3-adic selector for the incoming odd parent of a t=0 fatal entry

**Status:** exact necessary-condition reduction for the remaining odd-parent family in the special \(t=0,L=K+1\) fatal branch. It is not a reachability proof and has not been Lean-compiled.

Let \(K\ge266\), \(p=2^K\), and let \(h\) be the actual t=0 odd-exit source at level \(K\). The one-even-exit fatal-depth equation gives an odd \(r\) with
\[
40p+K-1-3h=(2K+7)2^{r+3}.
\]
Set
\[
D_0=8p+K-h,\qquad D_{\rm ent}=2^qD_0,\qquad
E=8p+K-D_{\rm ent}.
\]
Here \(E\) is the first entry at level \(K\), and \(q\) is the number of same-level even resets from \(E\) to \(h\). The t=0 source band gives \(D_0\ge2K+7\), and the level-K entry guard gives \(q\le K-1\).

The exact equation for \(D_0\) is
\[
3D_0=(2K+7)2^{r+3}-16p+2K+1.
\tag{1}
\]
The adjacent-fatal sector gives \(K\bmod6\in\{2,3\}\).

## 1. An immediate mod-3 obstruction and parity selector

For the incoming parent of \(E\) to be an odd reset with valuation \(t\), its output equation must satisfy
\[
2E+5=3^{t+1}d
\]
for an odd quotient \(d\). But
\[
2E+5=A_K-2^{q+1}D_0,\qquad
A_K:=16\cdot2^K+2K+5.
\tag{2}
\]
In both allowed sectors \(K\bmod6\in\{2,3\}\),
\[
A_K\equiv1\pmod3.
\]
Consequently:

- If \(D_0\equiv0\pmod3\), then \(2E+5\equiv1\pmod3\), so **E has no odd parent at all**.
- If \(D_0\equiv1\pmod3\), divisibility by \(3\) forces \(q\) odd.
- If \(D_0\equiv2\pmod3\), divisibility by \(3\) forces \(q\) even.

Combining the \(D_0\equiv0\pmod3\) case with the t=0 even-parent exclusion and the lower-level even-band argument in [T0-ODD-PARENT-SCALE-CONSEQUENCE.md](T0-ODD-PARENT-SCALE-CONSEQUENCE.md), the first level-K entry \(E\) has no ResetParent of either parity in these phase classes. By the root ResetParent equivalence, such an \(E\) cannot lie on the blank-root reset chain. This is conditional on the even-parent theorem being kernel-checked. The table identifies one third of residue-class pairs, but does not establish that one third of actual t=0 candidates occur in those classes.

The last two cases can be combined. Let \(\varepsilon\in\{0,1\}\) be the unique parity satisfying
\[
2^{\varepsilon+1}D_0\equiv1\pmod3.
\]
Thus \(\varepsilon=1\) when \(D_0\equiv1\), and \(\varepsilon=0\) when \(D_0\equiv2\). Write
\[
q=2m+\varepsilon,\qquad C:=2^{\varepsilon+1}D_0.
\]
Then \(C\equiv A_K\equiv1\pmod3\), and (2) becomes
\[
2E+5=A_K-C4^m.
\tag{3}
\]

## 2. Unique 3-adic residue for q at each incoming valuation

For a proposed incoming odd-reset valuation \(t\), the divisibility condition is
\[
3^{t+1}\mid A_K-C4^m.
\tag{4}
\]
Since \(A_KC^{-1}\equiv1\pmod3\), and the powers of \(4\) form the full subgroup of units congruent to \(1\pmod3\) modulo \(3^{t+1}\), there is exactly one residue
\[
m\pmod{3^t}
\]
satisfying (4). Therefore the incoming odd-parent valuation \(t\) selects exactly one residue
\[
\boxed{q\equiv q^{\rm in}_{K,r}(t)\pmod{2\cdot3^t},\qquad
q^{\rm in}_{K,r}(t)=2m_t+\varepsilon.}
\tag{5}
\]
For \(t=0\), this reduces to the parity condition. For \(t\ge1\), the compatible residues are obtained by the same Hensel lift as the Q-depth selectors:
\[
m_{n+1}=m_n+e_n3^n,\qquad
e_n\equiv
\frac{A_K-C4^{m_n}}{3^{n+1}}C^{-1}\pmod3,
\]
starting with \(m_0=0\) modulo \(1\).

Because \(q\le K-1\), whenever \(2\cdot3^t>K-1\), the residue (5) fixes \(q\) as an actual integer: either the unique residue lies in \([0,K-1]\), or no incoming parent of valuation \(t\) is possible. This can sharply reduce the remaining search before checking the dyadic source band.

## 3. The D0 phase table

Equation (1) determines \(D_0\bmod3\) from \(K\bmod18\) and \(r\bmod6\). The period is \(18\) in \(K\) and \(6\) in \(r\), because the calculation only uses \(2^K\) and \(2^{r+3}\) modulo \(9\).

For the allowed \(K\bmod6\in\{2,3\}\) and odd \(r\), the exact table is:

| \(K\bmod18\) | \(r\bmod6=1\) | \(r\bmod6=3\) | \(r\bmod6=5\) |
|---:|---:|---:|---:|
| 2 | 0 | 2 | 1 |
| 3 | 2 | 0 | 1 |
| 8 | 2 | 1 | 0 |
| 9 | 1 | 2 | 0 |
| 14 | 1 | 0 | 2 |
| 15 | 0 | 1 | 2 |

Thus one third of the \((K\bmod18,r\bmod6)\) phase pairs have \(D_0\equiv0\pmod3\) and are excluded immediately by (2). In the remaining phases, the parity of \(q\) is fixed before any source-level search.

### Reproducer and small phase checks

The companion [t0_entry_odd_parent_selector.mjs](t0_entry_odd_parent_selector.mjs) uses the logarithmic depth bound in [T0-SAME-LEVEL-DEPTH-LOG-BOUND.md](T0-SAME-LEVEL-DEPTH-LOG-BOUND.md) to enumerate only the \(O(\log K)\) parity-compatible \(q\)-values, then computes the exact incoming valuation \(t=v_3(2E+5)-1\) and checks the dyadic source band. Its sample checks include:
- \(K=267,r=259\): \(D_0\equiv0\pmod3\), so no incoming odd parent is possible.
- \(K=309,r=301\): \(q=0,t=1\) gives an incoming odd parent from level \(L=308\).
- \(K=333,r=325\): \(q=1,t=0\) gives an incoming odd parent from level \(L=332\).
- \(K=542,r=533\): two distinct entries are locally possible, \((q,t)=(1,1)\) and \((3,0)\), both with incoming source level \(L=541\).

The latter two are valid local inverse-grammar edges only; they do not assert blank-root reachability.

## 4. Composition with the incoming-level scale bound

If the even-parent exclusion is applied to the first level-K entry \(E\), any remaining immediate parent must be odd. For its source level \(L\), valuation \(t\), and quotient \(d\), the existing odd-parent scale theorem gives
\[
t\le L,\qquad 2^{K-2}<3^L,
\]
and the first-entry upper guard gives \(L\le K-1\). The complete necessary conditions for an incoming odd parent are therefore:

1. \(D_0\not\equiv0\pmod3\);
2. \(q\) has the parity prescribed above;
3. \(q\) satisfies the unique residue (5) for its incoming valuation \(t\);
4. the resulting \(d=(A_K-C4^m)/3^{t+1}\) has \(2^td\) in a dyadic source band at some \(L\) with \(t\le L\le K-1\) and \(2^{K-2}<3^L\).

The selector does not establish the source band or blank-root ancestry. It is a new arithmetic filter on the remaining odd-parent family, not a proof that the t=0 branch is impossible.
