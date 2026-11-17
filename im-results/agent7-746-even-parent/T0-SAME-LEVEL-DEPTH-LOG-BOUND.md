# Logarithmic bound on the same-level even-reset depth in the t=0 fatal branch

**Status:** exact arithmetic lemma conditional only on the t=0 fatal-depth equation and the level-K source/entry bands. No Lean compile is claimed.

Let \(K\ge266\), \(p=2^K\), and \(c=2K+7\). In the special \(t=0,L=K+1\) adjacent-fatal branch, let \(h\) be the t=0 odd-exit source at level \(K\), and let \(r\) be the odd fatal-tail depth. The exact fatal-depth equation is
\[
B_0:=40p+K-1-3h=c\,2^{r+3}.
\tag{1}
\]
The source-level certificate gives
\[
4p-K-4\le h\le8p-K-6.
\tag{2}
\]
Let \(D_0=8p+K-h\), and let \(E\) be the first level-K entry before \(q\) same-level even resets reach \(h\):
\[
E=8p+K-2^qD_0.
\tag{3}
\]
The entry lower guard is \(E\ge4p-K-4\).

## Claim

\[
\boxed{2^q\le\frac{15(2K+7)}{16}<2K,\qquad q\le\lfloor\log_2(2K)\rfloor.}
\tag{4}
\]
Thus the number of same-level even resets before the t=0 odd exit is logarithmic in the level \(K\), not linear in \(K\).

## Proof

From (1) and the upper bound on \(h\) in (2),
\[
B_0\ge40p+K-1-3(8p-K-6)
=16p+4K+17>16p.
\tag{5}
\]
From the lower bound on \(h\),
\[
B_0\le40p+K-1-3(4p-K-4)
=28p+4K+11.
\tag{6}
\]
For \(K\ge266\), \(28p+4K+11<32p=2^{K+5}\). Since \(c\ge1\) and \(B_0=c2^{r+3}\), this implies \(r+3\le K+4\). Hence
\[
2^{r+3}\mid 2^{K+4}=16p.
\tag{7}
\]
By (5), \(B_0-16p\) is a positive integer multiple of \(2^{r+3}\), so
\[
B_0-16p\ge2^{r+3}.
\]
Equation (1), rewritten as
\[
3D_0=B_0-16p+2K+1,
\]
therefore gives
\[
D_0\ge\frac{2^{r+3}}3
=\frac{B_0}{3c}
\ge\frac{16p}{3c}.
\tag{8}
\]
Finally, (3) and the entry lower guard imply
\[
2^qD_0
=8p+K-E
\le4p+2K+4.
\]
Using (8),
\[
2^q
\le\frac{3c(4p+2K+4)}{16p}.
\tag{9}
\]
For \(K\ge266\), \(2K+4\le p\), so \(4p+2K+4\le5p\). Thus
\[
2^q\le\frac{15(2K+7)}{16}<2K,
\]
where the last inequality holds for \(K\ge53\). This proves (4).

## Consequence for the incoming odd-parent search

The incoming odd-parent selector already forces \(q\) to one parity when \(D_0\not\equiv0\pmod3\), and excludes odd parents entirely when \(D_0\equiv0\pmod3\). Combining that parity condition with (4), there are at most
\[
1+\left\lfloor\frac12\log_2(2K)\right\rfloor
\]
possible \(q\)-values to test for a fixed t=0 fatal source. For each \(q\), the incoming valuation is fixed as \(t=v_3(2E+5)-1\), and the source level is uniquely determined by the dyadic band. Thus the remaining local odd-parent test can be reduced to \(O(\log K)\) candidates per fatal source, rather than a scan over all \(q<K\) or all pairs \((q,t)\).

This is a source/entry arithmetic bound; it does not prove that any surviving parent source is blank-root reachable.
