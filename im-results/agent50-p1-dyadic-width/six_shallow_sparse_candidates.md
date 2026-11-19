# Power-saving sparsity of six-shallow wall candidates

**Status:** paper proof from the exact pair-carry recurrence; intermediate result, not a BB(6) decision. The argument gives a power-saving bound on the *number* of parameters admitting a six-shallow subset. It does not exclude every parameter.

## Statement

Let \(\mathcal W_X\) be the set of integers \(14\le n\le X\) for which there is a subset \(A\subseteq\{0,\ldots,n-1\}\), with \(0\in A\), satisfying
\[
\sum_{s\in A}(n+3+s)2^s\equiv1\pmod{2^n},
\]
and having at most five consecutive-selected-position gaps of length 1 or 2.

Then
\[
\boxed{|\mathcal W_X|=O\!\left(X^{0.8881}(\log X)^5\right).}
\]
In particular, the set of six-shallow wall candidates has natural density zero, with a power saving. The same bound applies, up to a constant, to feeder parameters \(q\) with \(n=16q+14\).

This is not a uniform logarithmic bound on every no-short run: exceptional parameters may still exist, and the result does not settle the P1 wall or BB(6).

## 1. Exact residue class for a fixed pair word

For even n, the original carry condition forces \\(n\\equiv2\\pmod4\\), so \\(a_0=(n+2)/4\\) is integral. Do **not** assume \\(n\\equiv14\\pmod{16}\\): that stronger residue follows only when the first pair is itself no-short, whereas the prefix counted here may begin with one of the at most five short-gap pair positions.\n\nUse the paired carry recurrence from [no_short_pair_recurrence.md](no_short_pair_recurrence.md). At pair index \(k\), let \((x_k,y_k)\in\{0,1\}^2\) be the two selected bits, put
\[
\delta_k=x_k+2y_k,\qquad \gamma_k=y_k,
\]
and write \(H_k=n/2+k+2\). The exact pair recurrence is
\[
4a_{k+1}=a_k+\delta_k H_k+\gamma_k,
\qquad a_0=(n+2)/4.
\]
For any *fixed* pair word of length \(L\), iteration gives
\[
4^{L+1}a_L=A_L n+B_L,
\]
where
\[
A_L=1+\sum_{k<L}2\delta_k4^k,
\qquad
B_L=2+\sum_{k<L}(\delta_k(k+2)+\gamma_k)4^{k+1}.
\]
The coefficient \(A_L\) is odd. Therefore integrality of the carry path requires
\[
A_Ln+B_L\equiv0\pmod{4^{L+1}},
\]
which specifies exactly one residue class modulo \(4^{L+1}\). The condition is only necessary for a fixed word, which is all that is needed for an upper bound.

This formula includes all four pair patterns: 00, 10, 01, and 11. Thus it also applies to prefixes containing short-gap pair positions.

## 2. Growth bound for no-short words

Let \(g\in\{0,1,2\}\) be the capped gap state from the pair-carry note. Ignoring arithmetic divisibility, the no-short transitions are
- from \(g=0\): only 00, to state 2;
- from \(g=1\): 00 to 2, or 01 to 0;
- from \(g=2\): 00 to 2, 10 to 1, or 01 to 0.

If \(Q_L(g)\) is the number of length-\(L\) no-short words starting at state \(g\), then
\[
\begin{pmatrix}Q_{L+1}(0)\\Q_{L+1}(1)\\Q_{L+1}(2)\end{pmatrix}
=
M\begin{pmatrix}Q_L(0)\\Q_L(1)\\Q_L(2)\end{pmatrix},
\qquad
M=\begin{pmatrix}0&0&1\\1&0&1\\1&1&1\end{pmatrix},
\]
with \(Q_0=(1,1,1)^T\).

Take
\[
w=\left(\frac{233}{500},\frac{341}{500},1\right)^T,
\qquad \lambda=\frac{43}{20}.
\]
Direct rational arithmetic gives
\[
Mw=\left(1,\frac{733}{500},\frac{1074}{500}\right)^T
\le \lambda w,
\qquad
\mathbf1\le\frac{500}{233}w.
\]
Consequently
\[
Q_L(g)\le\frac{500}{233}w_g\lambda^L\le3\lambda^L
\]
for every starting state \(g\) and every \(L\ge0\).

Now fix a total pair-prefix length \(L\) and allow at most five short-gap pair positions. Choose their positions in at most
\[
\sum_{j=0}^5\binom Lj=O(L^5)
\]
ways. Each such position has at most four pair patterns. The remaining positions form at most six no-short blocks; for each block, the preceding bound gives at most \(3\lambda^{\text{block length}}\) possibilities from any starting gap state. Thus the number of pair words of length \(L\) with at most five short-gap positions is at most
\[
C L^5\lambda^L
\]
for an absolute constant \(C\). This count deliberately ignores arithmetic restrictions and therefore safely overcounts valid words.

## 3. A long no-short run has a short-prefix witness

There are
\[
P=(n-2)/2
\]
complete pairs (bits 1,2 through \(n-3,n-2\)); omitting the final bit \(n-1\) cannot increase the number of short gaps.

At most five short gaps imply at most five pair positions that create a short gap. The remaining good positions split into at most six consecutive no-short runs. Hence some run has length at least
\[
\frac{P-5}{6}=\frac{n-12}{12}.
\]

Set
\[
r=\left\lceil\frac18\log_2 X\right\rceil.
\]
For \(n\ge12r+12\), at least one no-short run has length at least \(r\). Choose the **first** such run. Before it, there are at most five short pair positions and at most five no-short runs, each of length at most \(r-1\). The prefix ending after the first \(r\) transitions of the chosen run therefore has a length \(L\) satisfying
\[
r\le L\le5(r-1)+5+r=6r.
\]
It contains at most five short-gap pair positions.

The parameters \(n<12r+12\) contribute only \(O(\log X)\) possibilities and can be set aside.

## 4. Count the candidate parameters

For each length \(L\in[r,6r]\), there are at most \(C L^5\lambda^L\) possible pair-prefix words. Each word forces \(n\) into one residue class modulo \(4^{L+1}\), so at most
\[
X/4^{L+1}+1\le X/4^L+1
\]
integers \(n\le X\) can realize that word.

Therefore
\[
|\mathcal W_X|
\le O(\log X)+
C\sum_{L=r}^{6r}L^5\lambda^L\left(\frac{X}{4^L}+1\right).
\]
Since \(\lambda=21479/10000<4\), the two geometric sums are bounded by
\[
O\!\left(r^5X(\lambda/4)^r+r^5\lambda^{6r}\right).
\]
With \(r=\lceil(1/8)\log_2X\rceil\), the exponents of \(X\) in these terms are respectively
\[
1-\frac18\log_2\left(\frac4\lambda\right)
=0.88804208\ldots,
\qquad
\frac34\log_2\lambda
=0.82825249\ldots.
\]
The first dominates, proving
\[
|\mathcal W_X|=O\!\left(X^{0.8881}(\log X)^5\right).
\]

## Consequences and limitations

- The six-shallow necessary condition can hold only on a zero-density, power-sparse set of parameters.
- This gives a deterministic pruning principle for finite searches: candidate parameters are much sparser than the full interval.
- It does **not** show that \(\mathcal W_X\) is finite, nor that it is empty for large \(X\).
- It does **not** prove the pointwise \(O(\log n)\) no-short-run conjecture. A sparse exceptional family may still contain the actual P1 feeder parameters.
- The argument uses the exact pair-carry residue formula and gap automaton, not a probabilistic independence assumption.

**Validation status:** the inequalities and finite-state count above are a paper derivation. They have not yet been formalized in Lean or independently reviewed. Keep this in im-results until those steps are completed.
