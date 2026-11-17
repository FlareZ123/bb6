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
>\,4K+20.
\]
The upper inequality in (3) is equivalent to
\[
16p\left(c-\frac74\,2^a\right)\le(4K+8)2^a.
\]
If \(4c\le7\cdot2^a\), it holds immediately. If \(4c>7\cdot2^a\), integrality gives \(c-\frac74\,2^a\ge1/4\), so the left side is at least \(4p\). This exceeds \((4K+8)2^a\), since \(2^a\le c<2K+7\) and \(p=2^K>(K+2)(2K+7)\) for \(K\ge266\). Thus the upper inequality holds exactly when
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
