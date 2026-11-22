# Offset-two prime filter for the wide-band exceptions

**Status:** exact finite modular exclusions for the \(t=w+2\) second-parent offset. This is an intermediate computational result, not a uniform theorem for all \(r\), all offsets, or blank-root reachability.

## Necessary condition

For a first parent at valuation \(w\) and a second parent at \(t=w+k\), the quotient-free two-step congruence implies
\[
D_{w+k}\mid
y+(2^k-2)w+3-k+(2k-3)2^{k-1}.
\]
At \(k=2\), this specializes to
\[
D_{w+2}\mid y+2w+3. \tag{P2}
\]
Therefore, for any prime \(p\), if
\[
2^{w+3}+3\equiv0\pmod p
\quad\text{but}\quad
y+2w+3\not\equiv0\pmod p,
\]
then the candidate has no second parent at valuation \(w+2\).

## Exact finite results

The candidate set is the wide-band exception parametrization
\[
a-5=ks+e,\qquad r-1\le k\le2r-2,\qquad 0\le e\le d-2,
\]
with the two band inequalities, followed by the existing eleven-prime first-parent filter and the short odd-entry exclusion. The remaining candidates are exactly the forced-even exception set in Agent 20's audit.

| Family member | Forced-even exceptions | Prime bound | Excluded by (P2) | Remaining |
|---|---:|---:|---:|---:|
| \(r=50\) (\(j=0\)) | 28 | \(p\le1{,}000{,}000\) | **28** | **0** |
| \(r=160\) (\(j=1\)) | 105 | \(p\le1{,}000{,}000\) | 94 | 11 |
| \(r=160\) (\(j=1\)) | 105 | \(p\le10{,}000{,}000\) | **97** | **8** |

For \(r=50\), every one of the 28 candidates has an explicit prime witness. The table gives the parametrizing pair \((k,e)\), the prime \(p\mid D_{w+2}\), and the nonzero residue of \(y+2w+3\pmod p\).

| \(k\) | \(e\) | \(p\) | \((y+2w+3)\bmod p\) |
|---:|---:|---:|---:|
| 50 | 148 | 7 | 1 |
| 53 | 42 | 5 | 1 |
| 57 | 53 | 13 | 7 |
| 57 | 110 | 1009 | 11 |
| 59 | 10 | 5 | 1 |
| 59 | 69 | 405991 | 227526 |
| 60 | 98 | 7 | 2 |
| 65 | 38 | 1523 | 1303 |
| 65 | 103 | 7 | 2 |
| 66 | 86 | 5 | 1 |
| 67 | 63 | 7 | 2 |
| 70 | 38 | 5 | 3 |
| 70 | 108 | 7 | 4 |
| 71 | 91 | 7 | 3 |
| 74 | 70 | 5 | 1 |
| 77 | 31 | 7 | 6 |
| 79 | 102 | 7 | 3 |
| 80 | 38 | 5 | 1 |
| 80 | 118 | 7 | 2 |
| 85 | 38 | 5 | 4 |
| 85 | 123 | 7 | 2 |
| 86 | 52 | 7 | 4 |
| 89 | 142 | 7 | 3 |
| 90 | 38 | 5623 | 2641 |
| 90 | 128 | 7 | 2 |
| 92 | 22 | 5 | 3 |
| 93 | 41 | 7 | 1 |
| 96 | 134 | 7 | 2 |

For \(r=160\), the eight candidates not eliminated by any prime \(p\le10^7\) are
\[
(k,e)\in\{(190,218),(194,500),(238,100),(261,281),
(270,308),(292,66),(299,275),(314,452)\}.
\]
This is only a bounded-prime sieve: these eight are survivors of the tested filters, not examples of actual second parents.

## Reproduction

The self-contained Node.js script is offset_two_prime_filter.js. It uses only exact BigInt modular arithmetic and a sieve of trial primes; it never materializes \(2^a\) or \(D_{w+2}\) as giant integers. The recurrence for \(y\bmod p\) is evaluated modulo \(55p\) for \(p=5,11\), and modulo \(p\) with Fermat exponent reduction for other primes.

Run:
\`\`\`sh
node offset_two_prime_filter.js 50 1000000
node offset_two_prime_filter.js 160 10000000
\`\`\`

The filter is one-way and exact: every reported witness rules out that candidate by (P2). Failure to find a witness below the selected prime limit proves nothing. No Lean compilation is claimed.
