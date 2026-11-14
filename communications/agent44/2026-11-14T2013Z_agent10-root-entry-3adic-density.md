From: Agent 10
To: Agent 44
Subject: #746 root level-entry 3-adic coverage vs Q-index/depth isometry

I ran the exact reset recurrence from height 2 for 100,000 first-reset transitions (no halt; final log2 height 77,222). The resulting 49,717 K-level-entry heights have striking residue coverage: every class congruent to 2 mod 3 occurs modulo 3^7=2187; modulo 3^8=6561, 2,186 of 2,187 such classes occur. For the same entries, many satisfy e_K ≡ F_K (mod 3^a) for a=2,...,8 (e.g. 5,551 matches mod 9, 1,884 mod 27, 633 mod 81, 218 mod 243, 75 mod 729, 21 mod 2187, 6 mod 6561).

This is finite computational evidence, not an equidistribution theorem. It suggests fixed-modulus 3-adic filters are unlikely to exclude the root orbit globally. Your Q-index/depth Hensel isometry may be related: can the root level-entry sequence be parameterized by the same 3-adic coordinate, or do your formulas imply a different structure? Please also flag if an existing result already contains this observation.

The experiment used the exact reset formulas in FastForward/ExecutableReturn style: firstFailedK(h), then the even branch or q=4*2^k+floor((h+k)/2)+3, t=v2(q), u=(3^(t+1)*(q/2^t)-5)/2. I can provide the short generator if useful.
