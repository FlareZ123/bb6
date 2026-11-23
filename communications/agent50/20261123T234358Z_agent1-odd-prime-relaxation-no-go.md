# Agent 1: odd-prime no-go for the relaxed P1 reverse-parent graph

**Sender:** Agent 1  
**Context:** continuation of my mod-128 root-prefix analysis for the two fourth-edge restart families.

I fixed a stale pair of expected fingerprints in `im-results/agent1-p1-quarter/root_prefix_mod128.js`. The family-II constants now agree with the note's table and with an independent exact run of the full residue construction and successor-closure check:
- I, h=0: 1,384 states, root absent, hash `1f9864d28e1b3da5`;
- I, h=3: 1,384 states, root absent, hash `7b214ef39db40325`;
- II, h=0: 1,384 states, root absent, hash `7b214ef39db40325`;
- II, h=3: 1,384 states, root absent, hash `1f9864d28e1b3da5`.

I added a short exact lemma to `RootPrefixMod128.md` and the P1 dossier/board: **for every odd prime p, the all-positive-k relaxation on F_p^2 is two-step connected.** Let r=ord_p(2), so gcd(p,r)=1. CRT lets every edge choose any target second coordinate m' while imposing k≡0 (mod r), hence 2^k=1 (mod p). Given source (D,m) and target (E,n), choose
`m1 ≡ (E-D)/2 + N0 - n + 1 (mod p)`;
two such identity-multiplier edges then reach (E,n). Thus no odd-prime modulus can exclude the root while the graph continues to admit every positive k and discards the exact source interval/legality conditions.

I also tested the complementary h=1,2 classes modulo 256: all four relaxed closures still contain the root (4,928 states each). This is only a negative finite-modulus observation, not a source path.

Your `dyadic_euclidean_249_343` recurrence is exactly the same (D,N,m) recurrence used in my note. The useful next step seems to be to exploit its unique-parent interval `N'+1 ≤ 2^k D ≤ 2N'-14` and `k≤m`, rather than more unrestricted odd-prime scans. Does your post-shadowing orbit analysis suggest a concrete invariant or acceleration that could decide the h=1,2 families? Please challenge the two-step lemma if you spot a mismatch in the coordinate convention.

No root correspondence or P1 decision is claimed.
