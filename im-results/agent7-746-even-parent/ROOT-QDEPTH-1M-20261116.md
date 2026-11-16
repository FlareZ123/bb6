# One-million-reset t=1 Q-parent scan

**Status:** reproducible finite computation only. This is not an all-time proof and does not establish that machine #746 is nonhalting.

The exact reset recurrence was run from blank-root height \(h_0=2\) for 1,000,000 reset transitions. The standalone standard-library implementation is [root_qdepth_scan_1m.py](root_qdepth_scan_1m.py). It reproduces the existing 100,000-transition audit exactly on the overlapping prefix, including the single positive-\(B\), \(8(2K+7)\)-divisible candidate at zero-based transition 188.

## Summary

| Quantity | 1,000,000-transition result |
|---|---:|
| Completed reset transitions | 1,000,000 |
| t=1 odd sources, all sectors | 124,386 |
| t=1 sources with \(K\bmod6\in\{2,3\}\) | 41,501 |
| Positive \(B(K,q)\) in those sectors | 17,873 |
| Positive \(B\) divisible by \(8(2K+7)\) | 1 |
| Exact t=1 Q-parent matches \(B=(2K+7)2^{j+4}\), \(j\) even | 0 |
| Maximum odd-reset exponent observed | 18 |

The final state has \(K=776018\), height bit length \(776021\), and big-endian height SHA-256
\[
\texttt{28da83c4622d008cb4cc0efc14de2e0b548a11fcf7eaac2c0e39d360ced9854a}.
\]
The final level deficit has 2-adic valuation \(4\).

## The only odd-factor candidate

The sole positive-\(B\) source for which \(8(2K+7)\mid B\) occurs at zero-based transition 188 (the 189th reset), with
\[
K=152,\quad q=33138298132994636175269277626115847469285685575,
\]
\[
B=42917599938366575559265117043288566652328146864,\quad 2K+7=311.
\]
Its quotient is
\[
\frac{B}{8(2K+7)}
=17249839203523543231215883055984150583733178
=2\cdot8624919601761771615607941527992075291866589.
\]
Thus its 2-adic valuation is \(1\), but its odd part is not \(1\); it is not a power of two and cannot be a Q match. Modulo \(27\), the quotient is \(14=2^{17}\), whereas a power of two with 2-adic valuation \(1\) would have to be \(2^1=2\pmod{27}\). The 3-adic selector and 2-adic exponent therefore disagree already at this finite candidate.

No later source in the remaining 900,000 transitions even has \(8(2K+7)\mid B\).

## Reproduction and limitations

Run from the repository root:

\`\`\`sh
python3 im-results/agent7-746-even-parent/root_qdepth_scan_1m.py --steps 1000000
\`\`\`

The scan checks the exact source expression \(B=112\cdot2^K-2K-34-18q\) only on actual t=1 root transitions in the surviving \(K\bmod6\) sectors. A Q match would require \(B/(8(2K+7))=2^{j+1}\) with odd exponent \(j+1\). The computation found none.

This extends the previous finite prefix to one million reset transitions; it does not resolve the infinite root orbit, the other fatal branches, or BB(6). The all-time mathematical route remains the source/entry-deficit reductions in [T1-Q-PARENT-FATAL-REDUCTION.md](T1-Q-PARENT-FATAL-REDUCTION.md), with the arbitrary-depth synthetic inverse obstruction in [NESTED-ODD-PARENT-HENSEL.md](NESTED-ODD-PARENT-HENSEL.md).
