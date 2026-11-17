# Source derivation of the two t=0 growth bounds

**Status:** exact elementary inequalities intended to discharge the two growth hypotheses in Agent 10's T0EvenParentArithmetic.lean. This is an intermediate proof aid; no Lean compile is claimed.

Let \(K\ge266\), \(q\le K-1\), and let the corrected one-even-entry parameter satisfy
\[
K+3\le\delta\le2K+4,\qquad \delta=2^q e,\quad e\ge1.
\]
The fatal-depth source-band lower bound is
\[
(2K+7)2^{r+2}\ge8\cdot2^K+(2K+7)+3.
\tag{1}
\]

The arithmetic core requires
\[
4K+11<2^{r+3},\qquad
4K+11<2^{K-q+2}.
\tag{2}
\]
Both follow from the source premises; they need not be independent assumptions.

## Elementary power estimate

For every \(K\ge10\),
\[
2^K\ge K^3.
\tag{3}
\]
The base case is \(2^{10}=1024\ge1000\). If \(2^K\ge K^3\), then
\[
2^{K+1}\ge2K^3\ge(K+1)^3,
\]
because \(2K^3-(K+1)^3=K^3-3K^2-3K-1>0\) for \(K\ge10\).

For \(K\ge10\), the two polynomial inequalities
\[
16K^3>(2K+7)(4K+11),\qquad
2K^3>(K+2)(4K+11)
\tag{4}
\]
are immediate by expansion and \(K\ge10\). Combining (3) and (4) gives
\[
16\cdot2^K>(2K+7)(4K+11),
\tag{5}
\]
and
\[
2\cdot2^K>(K+2)(4K+11).
\tag{6}
\]

## First bound in (2)

Multiply (1) by \(2\):
\[
(2K+7)2^{r+3}
\ge16\cdot2^K+2(2K+7)+6
>16\cdot2^K.
\]
By (5),
\[
(2K+7)2^{r+3}>(2K+7)(4K+11).
\]
Since \(2K+7>0\), cancel it:
\[
\boxed{4K+11<2^{r+3}.}
\]

## Second bound in (2)

Since \(\delta=2^q e\), \(e\ge1\), and \(\delta\le2K+4\),
\[
2^q\le\delta\le2K+4=2(K+2).
\]
Using (6),
\[
2^{K+2}=4\cdot2^K
>2(K+2)(4K+11)
\ge2^q(4K+11).
\]
Because \(q\le K-1\), the exponent \(K-q+2\) is natural and
\(2^{K+2}=2^q2^{K-q+2}\). Cancel \(2^q>0\):
\[
\boxed{4K+11<2^{K-q+2}.}
\]

Thus the two hypotheses hpow_r and hpow_kq in
Agent10T0Parent.t0_entry_even_parent_arithmetic_no_solution follow
from the source-derived depth bound and the corrected \(\delta\)-bounds.
No additional search, parity assumption, or CI-specific premise is used.

## Formalization route

A short Lean dependency chain is:

1. Prove \(K^3\le2^K\) for \(K\ge10\) by induction, using the polynomial inequality \(2K^3\ge(K+1)^3\).
2. Discharge the two polynomial inequalities in (4) by nlinarith from \(10\le K\).
3. Multiply (1) by \(2\), combine with (5), and cancel the positive factor \(2K+7\) to obtain hpow_r.
4. Use \(2^q\le\delta\le2K+4\), (6), and \(2^{K+2}=2^q2^{K-q+2}\) to obtain hpow_kq.

The corrected upper endpoint \(2K+4\) is essential: do not reuse the earlier \(2K+3\) bound.
