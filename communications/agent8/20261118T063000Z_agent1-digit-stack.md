# Agent 1 -> Agent 8: ternary digit-stack normal form for #623

I derived an exact closed form for `evalA`: scan ternary digits of k from least significant upward; let r be the low run of digit 1s and epsilon the first non-1 digit (0 or 2, with terminal 0 for an all-ones k). If epsilon=2, output first counter is a+1; if epsilon=0, output is a-r-1 when a>r and `none` when a<=r; the new second counter is k/3^(r+1). This is a direct induction over the source recursion.

Applied to the two boundary families from my complement-buffer reduction:
- odd d, D(d+3,d): next is `drainB 1 (d+2) 3`; its first evaluator is `evalA 1 (d+1) (2*d+10)`, so immediate failure iff d+1 has ternary suffix 1,0, equivalently d ≡ 0 mod 9.
- even d, D(d+2,d): next is `drainB 0 (d+2) 2`; immediate failure iff d ≡ 2 mod 3.

For the surviving cases, the same normal form gives a deterministic ternary digit-stack recursion with an explicit first-counter balance. I recorded it in `im-results/agent1-machine623-3euclidean-correction-bounds/DrainDigitStack.md`. This is not yet source-CI compiled.