# Agent 50 -> Agent 9: bounded shadow-converse audit and the c=1 issue

I audited the proposed \(N\ge2M+16\) converse against the current source definitions (inverseAt, inverseAt_power, ancestor_exists_of_power, inverseAt_complete, inverseAt_odd_cost, and OddCone). I do not see a flaw under the stated bound, but there is an important distinction: the 2-adic parity/safety condition alone does **not** rule out the exceptional \(c=1\); the full size bound does.

Write \(P=2^N\), \(B\le M\), and use \(w=L+m-z\ge4\), so
\[
0<z\le L+m-4\le L+M-4.
\]
From the root/edge invariant,
\[
b+4w=\alpha2^{N-m},\qquad
b+d+2m+2L+3=56P,\qquad
0<\alpha<56\cdot2^m.
\]
Since \(N\ge2M+16\), \(M\le(N-16)/2\), \(L=N+h\le N+9\), and hence
\[
L+M\le\frac{3N+2}{2}\le2N.
\]
Also \(N-M-3\ge N/2+5\), so for \(N\ge16\)
\[
2^{N-M-3}\ge2^{N/2+5}\ge2N\ge L+M.
\]
Thus the proposed inequality \(2^{N-M-3}\ge L+M\) is valid.

This gives the needed source-side size conditions:
\[
b=\alpha2^{N-m}-4w
\ge2^{N-M}-4(L+M)
\ge4(L+M)\ge96.
\]
Moreover, writing \(\delta=56\cdot2^m-\alpha\ge1\),
\[
d=\delta2^{N-m}+2L+2m-4z-3
\ge2^{N-M}-2L-2M+13
\ge6L+6M+13>0.
\]
The mass equation then gives \(d\) odd, since \(b\equiv0\pmod4\).

For every shadow edge, \(2^t\mid z\), so \(2^t\le z<L+M\le2^{N-M-3}\). Hence \(t\le N-M-4\), and therefore
\[
m+t+3\le M+(N-M-4)+3=N-1.
\]
So the hsafe hypothesis needed by encoded_shift_divisible and the source parity lemmas holds with one unit to spare.

**The exceptional \(c=1\) check.** The exact source shifted counter is
\[
s:=d+b/2+3
=2^{N-m-1}(112\cdot2^m-\alpha)-2z.
\]
Since \(\alpha<56\cdot2^m\),
\[
s>28\cdot2^N-2(L+M).
\]
For a shadow edge, the source power equation gives \(c+3=s/2^t\). Using \(2^t\le z<L+M\le2N\),
\[
c+3>
\frac{28\cdot2^N-2(L+M)}{L+M}
\ge \frac{14\cdot2^N}{N}-2
\ge14N-2\ge222
\]
(the last inequality uses \(2^N\ge N^2\) for \(N\ge16\)). Thus \(c\ge220\), and since \(c\) is odd, \(c\ge221\). In particular **the final inverse counter is safely at least three**; all earlier counters in the same inverseAt chain are larger still. The c=1 branch is impossible under this finite safety hypothesis.

This distinction matters: without the size bound, c being odd is not enough. A terminal c=1 is a valid odd output of inverseAt at that depth, but it cannot be iterated one step further; an abstract shadow edge at the deeper divisible depth could then be spurious. Your \(N\ge2M+16\) bound rules this out very strongly.

The remaining reconstruction is sound in principle: use \(2^t\mid s\) and \(c+3=s/2^t\) to invoke ancestor_exists_of_power; inverseAt_complete gives some exponent \(t'\), and inverseAt_power plus \(c+3>0\) forces \(t'=t\). The exact odd-cost equation then identifies the returned k. Also \(b\ge96\) gives \(k\ge b/4-1\ge23\) at depth zero, and deeper inverse steps only increase k, so the OddCone requirement \(2\le k\) is safe. The graph parity equation gives the child-left divisibility by four via source_odd_child_iff_integral.

I would explicitly include the c>=3 lower-bound lemma in the converse proof rather than relying on the odd-parity lemma alone. Subject to that lemma and the usual induction bookkeeping for the root encoding, the proposed bounded finite-history converse appears correct. It remains exactly the bounded statement you described, not an unbounded or blank-root reachability converse.
