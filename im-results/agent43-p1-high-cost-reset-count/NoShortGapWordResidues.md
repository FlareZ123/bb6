# No-short selected-gap residue scan

**Status:** reproducible exploratory computation; not a proof of a logarithmic bound and not a BB(6) result.

This continues the selected-gap recurrence in [Agent50's no-short pair note](../agent50-p1-dyadic-width/no_short_pair_recurrence.md). It isolates the exact 2-adic condition on the initial parameter for a fixed no-short gap word.

## Exact residue for a fixed word

Let (g_0,ldots,g_{k-1}\ge 3), let (s_0=0), (s_{j+1}=s_j+g_j), and let (s_k=G) be the terminal position (not a selected start). Define
[
S=\sum_{j<k}2^{s_j},\qquad
T=\sum_{j<k}s_j2^{s_j},\qquad
D=GS-T,\qquad
\Delta=2^G-7S.
]
For (C_0=n+3), (b_0=-1), and
[
C_{j+1}=C_j+g_j,\qquad b_{j+1}=\frac{C_j+b_j}{2^{g_j}},
]
the exact prefix identity is (2^G b_k=SC_0+T-1). The terminal defect is
[
2^G(C_k-7b_k)=\Delta(C_0+G)+7(D+1).
]
Because the starts are separated by at least three, (S\le(2^G-1)/7); hence (Delta\) is positive and odd. Requiring the terminal state to remain extendable, (8\mid C_k-7b_k), therefore determines **one and only one** residue class:
[
\boxed{C_0\equiv -G-7(D+1)\Delta^{-1}\pmod{2^{G+3}}.}
]
The representative used in the scan is the least one with (C_0\ge17), corresponding to (n\ge14). The residue is always (1\pmod{16}), hence (n\equiv14\pmod{16}).

The congruence also implies (2^G\mid SC_0+T-1), so all intermediate (b_j) are integral: the later terms in the full numerator are multiples of (2^{s_j}). For each earlier edge, (g_j\ge3) gives (8\mid C_j+b_j), hence (8\mid C_j-7b_j). Positivity follows from the separated-start bound (S_j\le(2^{s_j}-1)/7) and (T_j\le s_jS_j). Thus each word's residue is an exact extendable no-short prefix condition, not a floating-point approximation.

## Exhaustive finite scan

[no_short_gap_word_residue_scan.cpp](no_short_gap_word_residue_scan.cpp) enumerates every composition of each (G=3,\ldots,57) into parts at least three. For every word it computes the unique residue, checks (Delta) is odd and the residue is (1\pmod{16}), and directly verifies the minimizing word's integer recurrence and terminal defect. It uses 64-bit arithmetic with modulus at most (2^{60}).

Reproduce with:

```sh
g++ -O3 -std=c++17 -o gap-scan no_short_gap_word_residue_scan.cpp
./gap-scan 57 > gap-scan.tsv
```

The scan covers **1,773,314,928** gap words in total. Selected minima:

| Total span (G) | Words | Least (C_0\ge17) | Minimizing gaps | Terminal (C_k-7b_k) |
|---:|---:|---:|---|---:|
| 31 | 27,201 | 34,993 | 4,6,7,3,7,4 | 19,568 |
| 47 | 12,322,413 | 8,967,937 | 8,3,3,3,6,7,3,3,3,5,3 | 840,816 |
| 48 | 18,059,374 | 10,530,369 | 6,8,5,5,3,5,4,9,3 | 1,297,144 |
| 51 | 56,849,086 | 8,967,937 | 8,3,3,3,6,7,3,3,3,5,7 | 8,460,040 |
| 56 | 384,377,665 | 151,641,089 | 7,4,3,3,8,4,3,7,3,7,7 | 143,275,312 |
| 57 | 563,332,848 | 1,327,639,841 | 3,3,5,3,4,4,6,9,3,4,4,3,3,3 | 1,378,808 |

The minimum of (C_0/2^{G/2}) over this finite scan is approximately (0.188985141), at (G=51). Thus the tempting uniform square-root estimate (C_0\ge\tfrac12 2^{G/2}) is already false. The finite minimum of (C_0/2^{0.45G}) is approximately (1.10676), also at (G=51); this is only a numerical pattern, not evidence for an all-(G) theorem.

The minimum as a function of (G) is not monotone: the same (C_0=8{,}967{,}937) occurs at both (G=47) and (G=51), with different terminal gaps. For a finite scan range, the relevant quantity for “span at least G” is the suffix minimum over H\ge G. Over H\le57, selected suffix minima are:

| Required span at least G | Least C_0 found with G\le H\le57 | Witness span H |
|---:|---:|---:|
| 31 | 34,993 | 31 |
| 39 | 2,731,585 | 42 |
| 45 | 8,967,937 | 51 |
| 52 | 151,641,089 | 56 |
| 57 | 1,327,639,841 | 57 |

This is only a finite-range envelope: words with H>57 could lower it, so it is not yet a global lower bound.

A greedy “take the largest currently admissible gap” strategy is also false. For C_0=1,249, the first gap 3 leads to C=1,252,b=156. At that state C+b=1,408=2^6\cdot22. Choosing the largest admissible gap 6 gives total span 9 and then stops; choosing 4 instead gives (C,b)=(1,256,88), where C+b=1,344=2^6\cdot21, and another gap 4 yields total span 11. Thus arbitrary switching cannot be discarded by a maximal-gap greedy argument.

## What remains to prove

The useful exact reduction is now a residue problem: for every separated gap word, bound from below the least representative of
[
-G-7(D+1)\Delta^{-1}\pmod{2^{G+3}}.
]
Any uniform estimate (C_0\ge c\lambda^G) with (lambda>1) would give a logarithmic bound on the total no-short span. The finite scan suggests such a bound may exist, but it neither proves one nor rules out a sparse exceptional family at larger (G). A proof or a counterexample family is the next mathematical target; do not promote the empirical exponent (0.45) to a theorem.
