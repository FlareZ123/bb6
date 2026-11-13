# Cancellation-feeder inverse-parent sieve: current synthesis

**Scope.** This note combines exact exclusions for immediate parents of the synthetic cancellation-feeder family. It is an intermediate research synthesis, not a claim that the Space Needle root reaches or avoids these feeders.

For \(r\ge1\), set
\[
a_r=(9^r+5)/2,\quad A_r=2^{a_r},\quad
P_0(A)=0,\quad P_{j+1}(A)=A^2P_j(A)+9^j(A-3),
\]
and \(X_r=A_rP_r(A_r)/2\). Every physical parent valuation \(u\) lies in \(0\le u<2ra_r\) and must satisfy
\[
2^{u+1}+3\mid A_rP_r(A_r)+3-2u.
\tag{1}
\]

## Two complementary kinds of exclusion

### A. Exact middle-band interval

[Agent 46's all-\(r\) middle-band theorem](../agent46-needle-midstrip/README.md) proves that no parent exists for
\[
u=a_r-1+s,\qquad
d_r\le s\le\left\lfloor\frac{a_r-d_r}{2r-2}\right\rfloor,
\quad
d_r=1+\lfloor\log_2(3^{2r-1})\rfloor,
\]
for every \(r\ge2\). This is a contiguous interval, not a residue-density estimate. Examples:
- \(r=5\): \(u=29,541,\ldots,33,215\), 3,675 valuations;
- \(r=6\): \(u=265,740,\ldots,292,292\), 26,553 valuations.

### B. Uniform modular residue filters

The existing Agent 20 work supplies \(E_5,E_7,E_{13}\), with combined residue density \(46/91\). The additional filters are:

| Prime | Required valuation cylinder | Necessary surviving residue | New density beyond prior filters |
|---:|---|---|---:|
| 11 | \(u\equiv2\pmod{10}\) | \(u\equiv w_{11,r}\pmod{11}\) | \(5/154\) |
| 19 | \(u\equiv3\pmod{18}\) | \(u\equiv w_{19,r}\pmod{19}\) | \(7/247\) |
| 29 | \(u\equiv18\pmod{28}\) | \(u\equiv w_{29,r}\pmod{29}\) | \(9/319\) |
| 61 | \(u\equiv35\pmod{60}\) | \(u\equiv w_{61,r}\pmod{61}\) | \(1/61\) |

The allowed residues \(w_{p,r}\) and complete derivations are in the linked prime-specific notes:
- [Modulo 11](../agent46-mod11-parent-sieve/README.md)
- [Modulo 19](../agent46-mod19-parent-sieve/README.md)
- [Modulo 29](../agent46-mod29-parent-sieve/README.md)
- [Modulo 61](../agent46-mod61-parent-sieve/README.md)

The filters have been arranged so each new density is counted outside the union of the earlier filters. The seven-prime residue sieve therefore excludes
\[
\frac{46}{91}+\frac5{154}+\frac7{247}+\frac9{319}+\frac1{61}
=\boxed{\frac{3162121}{5176094}\approx61.0909\%}
\]
of all predecessor-valuation residue classes, uniformly in \(r\). This is an asymptotic density over the joint period, not an exact finite-range proportion.

The middle-band theorem is independent of the modular density count and can remove additional valuations inside the physical interval. The two methods should be combined in finite audits, but their overlap must be counted rather than added blindly.

## What this does and does not establish

Established:
- an infinite-family contiguous no-parent band for every \(r\ge2\);
- four additional all-\(r\) modular filters (11, 19, 29, 61);
- a combined exact residue-class coverage of approximately \(61.09\%\) for the physical parent-valuation search.

Not established:
- absence of parents in the remaining residue classes or outside the middle band;
- unreachability of any cancellation feeder from the blank-start orbit;
- nonhalting of the Space Needle machine;
- the exact value of BB(6).

## Highest-value next work

1. Have Agent 20/48 adversarially review the new modular derivations and the quotient bounds.
2. Formalize the residue lemmas in Lean, reusing CancellationNat.P, CancellationNat.exact, and the existing physical-range/positivity lemmas.
3. Search for additional small primes \(p\) with \(-3\in\langle2\rangle\pmod p\), but measure incremental coverage after CRT overlap rather than raw density.
4. Combine the modular filters and the middle-band interval in finite \(r=5,6\) audits, preserving the exact surviving valuation list for any subsequent divisibility certificate.

All these artifacts remain in im-results/; none is a completed BB(6) proof.
