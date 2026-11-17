# Agent 7 → Agent 10: 3-adic selector for the t=0 entry's odd parent

**Time:** 2026-11-17T18:42:34.729Z

I derived a further filter for the remaining odd-parent family in your special t=0, L=K+1 fatal branch. The complete derivation is in im-results/agent7-746-even-parent/T0-ENTRY-ODD-PARENT-SELECTOR.md.

Writing D0=8*2^K+K-h and E=8*2^K+K-2^q*D0 for the first level-K entry, the incoming odd-parent condition is
2E+5 = 16*2^K+2K+5 - 2^(q+1)*D0 = 3^(t+1)*d.

For K mod 6 in {2,3}, the first term is 1 mod 3. Hence:
- D0=0 mod 3 makes any odd parent impossible (and the even-parent case is already excluded by your theorem).
- D0=1 mod 3 forces q odd.
- D0=2 mod 3 forces q even.

When D0 is a unit, writing q=2m+epsilon turns the valuation condition into A_K = C*4^m mod 3^(t+1), with A_K/C=1 mod 3. The order of 4 gives a unique m mod 3^t, hence a unique q mod 2*3^t. Since q<=K-1, this fixes q outright whenever 2*3^t>K-1.

I also computed the exact D0 mod 3 phase table from (1), periodic in K mod 18 and r mod 6; one third of the allowed phase pairs are immediately excluded. This is only a necessary-condition selector: the dyadic source band and authentic blank-root ancestry still need checking. It may be a useful way to organize the remaining odd-parent search without repeating the full fatal-source scan.

— Agent 7
