# Centered-Y middle-block diagnostic: 9,968-state extension

**Status:** finite BigInt replay, not an all-time proof. This extends the 100-state centered-Y observation in RootRayGapCocycle.md through the existing root trace \(D_{33},\ldots,D_{10000}\).

## Definition

For sector \(s\in\{LO,LE,RO,RE\}\), let
\[
c_s=(18,10,2,4),\qquad z=Y-c_s=2g-c_s.
\]
Let \(\ell\) be the least integer with
\[
\tau(\ell)=\frac{3^\ell-1}{2}\ge q+3,
\]
and put
\[
W=9\ell+22,\qquad W_Y=4W.
\]
Choose \(k,j\) least with \(3^k>W_Y\) and \(3^j>W_Y^3\). The tested middle block is the ternary digits of \(z\bmod 3^j\) in positions
\[
[k+2,j-2).
\]
It is nonmonochromatic exactly when it contains a digit different from 0 and a digit different from 2.

Negative z is handled using the Euclidean residue in \([0,3^j)\).

## 9,968-state result

A deterministic BigInt replay of the source-shaped high-level recurrence from \(D(0,7)\) gives:

- states checked: 9,968 (\(D_{33}\) through \(D_{10000}\));
- failures of the centered-Y middle-block predicate: **0**;
- \(\ell\) range: 9--1,936;
- \(W_Y\) maximum: 69,784;
- middle-block lengths: 7--16.

Length histogram:
\[
7:10,\ 8:78,\ 9:68,\ 10:234,\ 11:197,\ 12:694,\ 13:612,\ 14:2150,\ 15:1796,\ 16:4129.
\]

All 9,968 blocks contain both a nonzero digit and a digit different from 2.

## Bounded witness-position observations

Measure positions from the low edge of the middle block. Across the same trace:
- the first digit different from 0 occurs at offset at most **10**;
- the first digit different from 2 occurs at offset at most **9**.

Measured from the high edge:
- the last digit different from 0 is within **9** positions;
- the last digit different from 2 is within **8** positions.

Extremal examples:
| Witness | Index | Middle block | Offset / distance |
|---|---:|---|---:|
| latest first nonzero | 8643 | 0000000000102002 | 10 |
| latest first digit not 2 | 3382 | 22222222202112 | 9 |
| farthest last digit not 0 | 5497 | 202212000000000 | 9 |
| farthest last digit not 2 | 6211 | 0002220022222222 | 8 |

The bounded witness positions suggest a finite-prefix formulation: if one can prove that the first 11 digits after the low trim always contain both a nonzero and a non-2 digit, the entire middle-block condition follows without inspecting the growing high end.

However, the observed 11-digit prefixes are nearly all distinct: there are **9,723** distinct prefixes across 9,968 states, including 9,334 distinct length-11 prefixes among the 9,578 windows of length at least 11. The most frequent prefix occurs only three times. A proof by cataloguing observed prefix strings is therefore not promising; the low-prefix property needs a structural modular invariant or a compact transducer on the joint \((H,q)\) data.

## Research consequence

The centered-Y coordinate remains a promising candidate for excluding the terminal strip. The next mathematical step is not a larger empirical horizon; it is to derive a source-level recurrence for the first 11 ternary digits of \(z\) (or an equivalent pair of low residues), using
\[
Y'=|Y-2T|-6q',\qquad T=3D+2r+c_s,
\]
together with the D-free coordinate update for \(H\). The nearly injective observed prefix list argues against a raw prefix trie and in favor of an arithmetic/transducer invariant.

This file is an intermediate computational result, not a publishable theorem and not evidence that the #623 machine is nonhalting.
