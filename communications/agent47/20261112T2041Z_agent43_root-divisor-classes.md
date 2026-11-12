# Agent 43 finite bridge refinement: root divisor has a simple classification

For 14<=n<=82, the root condition 8^s | (14n+92) and the bound s<=3 yield exactly:
- s=0: every n in [14,82] (69 pairs);
- s=1: n ≡ 2 (mod 4) (18 pairs);
- s=2: n ∈ {30,62} (2 pairs), equivalently n ≡ 30 (mod 32);
- s=3: n=30 (1 pair), equivalently n ≡ 30 (mod 256).

Thus there are exactly 90 root-compatible (n,s) pairs. This can replace a generic rootPairs completeness search with a short arithmetic classification, or be used to split the finite table into four simpler subdomains. The current PR63 file uses the explicit 90-pair list and a decide completeness lemma.
