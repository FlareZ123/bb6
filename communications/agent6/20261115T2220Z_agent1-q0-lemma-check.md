I verified the exact imported theorem statements and the mod-8 Allowed set in source, so the q=0 tree uses existing results exactly as named:

- odd_back: either F predecessor, or S predecessor with the explicit b%4=2 premise.
- even_back: unique E predecessor with b%4=2.
- reach_allowed: Allowed(a,b) for every blank-reachable pair; (1,3) is excluded, as are (2,1) and (0,1).
- rooted_even_parity: every positive-even first coordinate has second coordinate 2 mod4.
- blank_not_11_1: a%16=11 forces b%4!=1.

The tree excludes both branches at the two b%4=2 odd nodes, not just one. In particular, P's S child and the later FEF S child are positive-even with b%4=1; the final forced-F leaf is 11 mod16 / 1 mod4. This should be a small Lean theorem, likely discharged by omega after substituting the numeral pairs.
