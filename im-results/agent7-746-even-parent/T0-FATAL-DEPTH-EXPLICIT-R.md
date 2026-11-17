# Explicit fatal-tail depth for the t=0 adjacent-fatal source

**Status:** exact characterization of the t=0 source-band/fatal-depth arithmetic candidate. It removes the search over \(r\), but does not establish blank-root reachability.

Let \(K\ge266\), \(p=2^K\), \(c=2K+7\), and
\[
a=\lfloor\log_2 c\rfloor,\qquad 2^a\le c<2^{a+1}.
\]
In the special t=0 adjacent-fatal branch, the source height \(h\) at level \(K\) and odd fatal-tail depth \(r\) satisfy
\[
B_0:=40p+K-1-3h=c\,2^{r+3}.
\tag{1}
\]
Because this is a t=0 odd-exit source, \(h+K\) is odd and its raw odd-reset parameter is
\[
d=4p+\frac{h+K-1}{2}+3
=4p+\frac{h+K+5}{2}.
\]
The source band \(6p+1\le d\le8p-1\) is therefore equivalent to
\[
4p-K-3\le h\le8p-K-7.
\tag{2}
\]
Substituting (2) into (1) gives
\[
16p+4K+20\le c\,2^{r+3}\le28p+4K+8.
\tag{3}
\]

## Explicit r

The unique possible exponent in (3) is
\[
\boxed{r+3=K+4-a,\qquad r=K+1-\lfloor\log_2(2K+7)\rfloor.}
\tag{4}
\]

Indeed, \(c<2^{a+1}\), so if \(r+3\le K+3-a\), then
\[
c2^{r+3}<2^{a+1}2^{K+3-a}=16p,
\]
contrary to (3). Also, \(c\ge2^a\), so if \(r+3\ge K+5-a\), then
\[
c2^{r+3}\ge2^a2^{K+5-a}=32p,
\]
again contrary to (3), since \(28p+4K+8<32p\) for \(K\ge266\). This proves (4).

## Exact existence criterion for the source-band candidate

With (4), the middle expression in (3) is
\[
c2^{K+4-a}=16p\frac{c}{2^a}.
\]
The lower inequality in (3) is automatic for \(K\ge266\): since \(c>2^a\),
\[
c2^{K+4-a}-16p
=(c-2^a)2^{K+4-a}
\ge2^{K+4-a}
>\frac{16p}{2K+7}
>4K+20.
\]
For the last inequality, use \(2^K\ge K^3\) for \(K\ge10\), followed by \(16K^3>(4K+20)(2K+7)\).
The upper inequality in (3) is equivalent to
\[
16p\left(c-\frac74\,2^a\right)\le(4K+8)2^a.
\]
If \(4c\le7\cdot2^a\), it holds immediately. If \(4c>7\cdot2^a\), integrality gives \(c-\frac74\,2^a\ge1/4\), so the left side is at least \(4p\). This exceeds \((4K+8)2^a\), since \(2^a\le c<2K+7\) and \(p=2^K>(K+2)(2K+7)\) for \(K\ge266\) (for example, use \(2^K\ge K^3\) for \(K\ge10\)). Thus the upper inequality holds exactly when
\[
\boxed{4(2K+7)\le7\cdot2^{\lfloor\log_2(2K+7)\rfloor}.}
\tag{5}
\]

The fatal-depth theorem also requires \(r\) odd. Combining (4) and (5), the t=0 source-band/fatal-depth arithmetic candidate exists exactly when
\[
\boxed{
K+1-\lfloor\log_2(2K+7)\rfloor\ \text{is odd},
\qquad
4(2K+7)\le7\cdot2^{\lfloor\log_2(2K+7)\rfloor}.
}
\tag{6}
\]
The K-sector condition \(K\bmod6\in\{2,3\}\) remains in force. It ensures the numerator defining \(h\) in (1) is divisible by \(3\); since \(r\) is odd, \(c2^{r+3}\) is divisible by \(16\), and (1) modulo \(4\) gives \(h+K\equiv1\pmod4\), as required for the odd exit.

Equivalently, for a fixed \(a\ge9\), the candidate levels are exactly
\[
2^{a-1}-3\le K\le7\cdot2^{a-3}-4,
\]
with \(K\equiv2\pmod6\) if \(a\) is even and \(K\equiv3\pmod6\) if \(a\) is odd. This follows by rewriting \(2^a\le2K+7\), \(4(2K+7)\le7\cdot2^a\), and \(K-a\) even.

Finally, the deficit at the odd-exit source is now explicit:
\[
\boxed{
D_0=8p+K-h
=\frac{(c-2^a)2^{K+4-a}+2K+1}{3}.
}
\tag{7}
\]
This formula can be substituted directly into the incoming-entry parity/3-adic selector and the logarithmic q bound. No search over \(r\) is needed.

This characterizes only the t=0 source candidate. The incoming parent of the first level-K entry and its blank-root ancestry remain separate obligations.


## Parity-sharpened logarithmic bound on q

Write \(\delta=c-2^a\). Since \(r=K+1-a\) is odd, \(K-a\) is even. The allowed \(K\)-sector therefore gives:

- If \(K\equiv2\pmod6\), then \(a\) is even, \(c\equiv11\pmod{12}\), and \(2^a\equiv4\pmod{12}\). Hence \(\delta\equiv7\pmod{12}\), so \(\delta\ge7\).
- If \(K\equiv3\pmod6\), then \(a\) is odd, \(c\equiv1\pmod{12}\), and \(2^a\equiv8\pmod{12}\). Hence \(\delta\equiv5\pmod{12}\), so \(\delta\ge5\).

Using (7), \(D_0=(\delta2^{K+4-a}+2K+1)/3\), and the entry lower guard \(2^qD_0\le4p+2K+4\), we obtain the following sharper bounds.

If \(K\equiv2\pmod6\), then
\[
2^q
<\frac{3(4p+2K+4)}{7\cdot2^{K+4-a}}
=\frac{3(4p+2K+4)}{112p}\,2^a
<2^{a-3},
\]
where the last inequality is equivalent to \(p>3K+6\), true for \(K\ge266\). Thus \(q\le a-4\).

If \(K\equiv3\pmod6\), then
\[
2^q
<\frac{3(4p+2K+4)}{5\cdot2^{K+4-a}}
=\frac{3(4p+2K+4)}{80p}\,2^a
<2^{a-2},
\]
where the last inequality follows from \(p>(3K+6)/4\), also true for \(K\ge266\). Thus \(q\le a-3\).

In summary,
\[
\boxed{
q\le
\begin{cases}
a-4,&K\equiv2\pmod6,\\
a-3,&K\equiv3\pmod6.
\end{cases}}
\tag{8}
\]
After the forced parity of \(q\) is applied, at most \(\lceil(a-3)/2\rceil\) candidates remain for each t=0 fatal source. This improves the uniform \(q\le a-1\) bound.
