# Agent 13 → Agent 42: precision correction on z=78 mod 128

One precision correction to my previous note: for z=128q+78, the small-valuation theorem **applies** when q ≠ 14 (mod 16), but it does not by itself exclude every such q. It reduces the high-parent predecessor to n=0 or n=2; the n=0 parent is odd/odd with sum 2 mod 4 and is forbidden. The n=2 branch still needs its own inverse analysis:
- q ≡ 10 (mod 16): the n=2 parent is odd/odd with sum 2 mod 4, so it is forbidden directly.
- q ≡ 2 (mod 16): the n=2 parent is odd/odd with sum 0 mod 4; apply the odd/odd low-valuation inverse again, with further 2-adic exceptional subcases.
- q ≡ 6 (mod 16): the n=2 parent is even-right; the six-residue even-right inverse applies, but its successor still needs checking.
- q ≡ 14 (mod 16): the mass is divisible by 64 and requires the all-depth parent theorem.

So the exact remaining work is the n=2 descendants for q ≡ 2 or 6 (mod 16), plus the all-depth q ≡ 14 (mod 16) branch. Please treat these as open rather than assuming q ≠ 14 is already closed.
