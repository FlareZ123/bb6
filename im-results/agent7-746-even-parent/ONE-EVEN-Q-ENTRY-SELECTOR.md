# One-even-reset Q-entry depth selector

**Status:** exact arithmetic reduction and elementary 3-adic selector. This does not decide the #746 blank-root orbit or BB(6). Keep in \`im-results/\`.

## 1. The missing distinction between the level entry and the Q source

Use the exact t=1 Q-parent equation from [ROOT-QDEPTH-ALIGNMENT.md](ROOT-QDEPTH-ALIGNMENT.md):
\[
B(K,q)=112\cdot2^K-2K-34-18q
      =(2K+7)2^{j+4},
\]
where \(q\) is the *actual outgoing odd-edge source* at level \(K\), not necessarily the level-entry height.

Let \(h\) be the level-entry height and \(p=2^K\). The previous all-time reduction shows that a genuine Q match has either zero or one same-level even reset. In the one-reset case,
\[
q=4p+\frac{h+K}{2},\qquad D_{\rm in}=2D_Q,
\]
where \(D_{\rm in}=8p+K-h\) and
\[
D_Q=\frac{32p+20K+34+(2K+7)2^{j+4}}{18}.
\]

For \(K\ge10\), the level entry in a genuine Q match is produced by a preceding odd reset. Write its exact source exponent and odd quotient as
\[
2h+5=3^{s+1}d_0,\qquad d_0\text{ odd}.
\]
Substituting \(D_{\rm in}=2D_Q\) gives
\[
18(8p+K-h)=2(32p+20K+34+(2K+7)2^{j+4}),
\]
hence
\[
\boxed{
E_K(j):=80\cdot2^K-22K-23-2(2K+7)2^{j+4}
      =18h+45=3^{s+3}d_0.
}
\tag{1}
\]
In particular, if \(r_0=v_3(d_0)\), then
\[
3^{s+3+r_0}\mid E_K(j),\qquad v_3(E_K(j))=s+3+r_0.
\]

This is the correct high-precision condition for the one-even-reset branch. It is **not** the same as applying the existing Q-depth selector to \(Q_j(K+2)=9(2q+5)\) with precision \(s+2+r_0\). Indeed, since \(h\equiv2\pmod3\) and \(K\bmod6\in\{2,3\}\),
\[
2q+5=8p+h+K+5\equiv2\pmod3.
\]
Thus \(v_3(Q_j(K+2))=2\) exactly in this branch, regardless of \(s\) and \(r_0\). The incoming odd-reset valuation belongs to \(E_K(j)=9(2h+5)\), not to the outgoing Q numerator.

For comparison, in the zero-even-reset branch \(q=h\), the exact source identity is
\[
Q_j(K+2)=9(2h+5)=3^{s+3}d_0;
\]
equivalently, the dyadic equation is \(B(K,h)=(2K+7)2^{j+4}\). The existing Q-depth selector applies directly to \(Q_j\). The two cases therefore have distinct, but parallel, 3-adic selectors.

## 2. Unique selector for the one-even-reset branch

Put
\[
A_K=80\cdot2^K-22K-23,\qquad C_K=32(2K+7).
\]
For \(K\equiv2\) or \(3\pmod6\),
\[
A_K\equiv C_K\not\equiv0\pmod3.
\]
For \(K\equiv2\pmod6\), both residues are \(1\); for \(K\equiv3\pmod6\), both residues are \(2\).

Writing \(j=2r\), equation (1)'s divisibility condition becomes
\[
3^{k+1}\mid E_K(2r)
\quad\Longleftrightarrow\quad
4^r\equiv A_K C_K^{-1}\pmod{3^{k+1}}.
\tag{2}
\]
The right side is a unit congruent to \(1\pmod3\).

For every \(k\ge1\), the powers of \(4\) form the entire subgroup of units congruent to \(1\pmod3\) modulo \(3^{k+1}\). The key exact lift is
\[
4^{3^m}\equiv1+3^{m+1}\pmod{3^{m+2}}.
\tag{3}
\]
It follows by induction from \(4=1+3\). In particular, \(4\) has exact order \(3^k\) modulo \(3^{k+1}\), while that subgroup has exactly \(3^k\) elements.

**Theorem.** For every \(K\ge0\) with \(K\bmod6\in\{2,3\}\) and every \(k\ge1\), there is exactly one even residue
\[
j\pmod{2\cdot3^k}
\]
such that \(3^{k+1}\mid E_K(j)\).

The residues are compatible as \(k\) increases. Thus the incoming odd exponent \(s\) and quotient valuation \(r_0\) select the unique residue
\[
j\equiv J^{(1)}_K(s+2+r_0)
\pmod{2\cdot3^{s+2+r_0}},
\]
where \(J^{(1)}_K(k)\) denotes the selector in the theorem.

### Explicit Hensel digit

Let \(r_m\) be the unique solution modulo \(3^m\), starting with \(r_0=0\). Define
\[
e_m\equiv
\frac{A_K-C_K4^{r_m}}{3^{m+1}}\,C_K^{-1}
\pmod3.
\]
The quotient is integral by the induction hypothesis. Then
\[
r_{m+1}=r_m+e_m3^m
\]
is the unique lift modulo \(3^{m+1}\). To verify it, use (3):
\[
4^{r_m+e_m3^m}
\equiv4^{r_m}(1+e_m3^{m+1})
\pmod{3^{m+2}},
\]
so the new residual vanishes modulo \(3^{m+2}\) for exactly one digit \(e_m\in\{0,1,2\}\).

For fixed precision \(k\), the selector is periodic in \(K\) with period \(2\cdot3^{k+1}\): \(2^K\) has order \(2\cdot3^k\) modulo \(3^{k+1}\), while the linear \(K\)-terms have period \(3^{k+1}\).

## 3. Relation to the existing phase table

At \(k=2\), the condition is \(27\mid E_K(j)\), exactly the existing W1m27 condition in [QPhaseTable.lean](QPhaseTable.lean). The unique \(j\bmod18\) values therefore reproduce its candidates1 table:

| \(K\bmod54\) | \(j\bmod18\) |
|---:|---:|
| 2 | 6 |
| 3 | 0 |
| 8 | 4 |
| 9 | 14 |
| 14 | 2 |
| 15 | 10 |
| 20 | 0 |
| 21 | 6 |
| 26 | 16 |
| 27 | 2 |
| 32 | 14 |
| 33 | 16 |
| 38 | 12 |
| 39 | 12 |
| 44 | 10 |
| 45 | 8 |
| 50 | 8 |
| 51 | 4 |

At the next precision \(k=3\), sample exact residues are:
\[
\begin{array}{c|rrrrrrr}
K&2&3&8&9&14&15&26\\
\hline
j\bmod54&6&18&4&32&20&10&16
\end{array}
\]
The selector's period in \(K\) is then \(162\), not \(54\).

The synthetic \(K=26,j=16\) witness in [QPhaseCounterexample.lean](QPhaseCounterexample.lean) checks the distinction exactly. Its entry is \(h=291387584\), produced by an incoming \(s=1\) odd reset with \(d_0=64752797\). The one-even-reset numerator is
\[
E_{26}(16)=5244976557=3^4\cdot64752797,
\]
so the \(k=s+2=3\) selector gives \(j\equiv16\pmod{54}\). After the even reset, \(q=414129261\) and \(2q+5=828258527\equiv2\pmod3\), hence \(v_3(Q_j(28))=2\), not \(4\). This is a synthetic inverse-grammar witness, not a blank-root path.

The companion [one_even_q_entry_selector.mjs](one_even_q_entry_selector.mjs) computes the compatible residues by the explicit lift and brute-checks uniqueness for \(K\) in the 18 displayed classes and \(1\le k\le5\). This finite check is a reproducibility aid, not the proof.

## 4. Scope and next use

This removes a notation ambiguity in the root/Q-depth composition: when there is one same-level even reset, the incoming odd exponent must be applied to \(E_K(j)\), not to \(Q_j(K+2)\). The resulting selector is an exact coordinate form of the same Q-alignment equation, not an independent obstruction and not a new root exclusion.

The useful next step is to integrate this split into the root-entry analysis: use the ordinary Q-depth selector for \(m=0\), the entry selector above for \(m=1\), and compare the selected residue with the actual dyadic odd-part equality \(B(K,q)=(2K+7)2^{j+4}\). Any claimed exclusion must still use the authentic blank-root entry data; synthetic selector solutions are not root paths.
