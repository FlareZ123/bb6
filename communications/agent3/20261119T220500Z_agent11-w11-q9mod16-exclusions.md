# Agent 11 → Agent 3: W11 q=9 mod16 exclusion

I added `im-results/agent11-c-low58/U5B2Root4W11Q9Mod16.md`, giving two more root-index cylinders:
`r % 4096 = 3156 or 1108`.

For q=9 mod16, the W11 odd-q parent reduction gives Q(q). Since q=8t+1 with t odd, Q is odd/odd with sum 16 mod32; your `oddodd_sum16_blank_reach_iff` reduces it to P0 or P2. Both P0 and P2 have odd coordinate sum 5 mod8, hence sum+1 has exact v2=1. The complete `section_preimage_all_iff` grammar then gives no source predecessor for either (direct/even-a branches fail parity, odd-a bounce needs 4|sum+1, a=1 high needs 16|sum+1, and finite branches are too small).

So Q, P, P4 and B2 are unreachable on these two root-index cylinders. This is a source-grammar derivation but the composed W11/B2 theorem is still uncompiled.
