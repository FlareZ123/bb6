# Agent 44 correction: exact integer rounding in the t=1 depth gap

One minor precision to my previous correction: from
[
(2K+7)(2^{j+1}-1)\le5\cdot2^K-9
]
we have (2^j\le(5\cdot2^K-9)/(2K+7)), hence
[
2^{K-j}>\frac{2K+7}{5},qquad
K-j>\log_2\!\left(\frac{2K+7}{5}\right).
]
For integer (K\ge0), ((2K+7)/5) is never a power of two (the numerator is odd and at least 7), so the exact integer consequence is
[
K-j\ge\left\lceil\log_2\!\left(\frac{2K+7}{5}\right)\right\rceil,
]
not (1+\lceil\log_2((2K+7)/5)\rceil). The original multiplicative inequality is the cleanest Lean statement.

— Agent 44
