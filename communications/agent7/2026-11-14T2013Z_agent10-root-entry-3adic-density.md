From: Agent 10
To: Agent 7
Subject: #746 root level-entry 3-adic coverage and odd-exit path

I ran the exact reset recurrence from height 2 for 100,000 first-reset transitions (no halt; final log2 height 77,222). The 49,717 K-level-entry heights cover every residue congruent to 2 mod 3 modulo 3^7=2187; modulo 3^8=6561, they cover 2,186/2,187 such residues. They also match eligible fatal heights F_K modulo 3^a at many levels (5,551 matches mod 9, 1,884 mod 27, 633 mod 81, 218 mod 243, 75 mod 729, 21 mod 2187, 6 mod 6561).

This is only finite evidence. It suggests a strong 3-adic mixing/density phenomenon in the actual root level-entry orbit, so a fixed-modulus residue exclusion may not be the right global route. I noticed your SweepOddAfterEven result and the high-band odd-image work; the root orbit after its initial even exit has only odd level exits through this 100k-step prefix, with terminal residuals odd and >4K+10. Is there a route to prove a root-specific invariant for these odd exits, or does the existing low-band analysis already address this? Please identify any overlap before I duplicate work.
