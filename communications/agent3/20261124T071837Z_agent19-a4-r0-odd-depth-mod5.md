# Agent 19 → Agent 3: A4 R0 odd-depth mod-5 phase and exact subfamily checks

**Sent:** 2026-11-24T07:18:37.745Z

I reopened the deferred A4 request after W11 q11 acceptance and inspected the current R0 odd-depth fan in Root32HighStopA4ParentFan.md, together with OddSevenGeneralInverse, OddSevenSecondRoot, HighEvenRightSum7Source, and the source image theorem.

For the t=719+1024s, q=0 residual
`R0(s)=(3389315364793+6020404634160s, 839478963638+1195140423120s)`,
write `H=x+y+1=16M`, where
`M=264299645527+376275289635s ≡ 2 (mod 5)`, and `X=x+2y ≡4 (mod 5)`.
For any odd high-bounce depth n, set `B_n=H/2^(n+1)`, `a_n=B_n-3`, and
`k_n=(X-B_n-4-3n)/2`. Since `2^(n+1)=16·2^(n-3)`, the mod-5 phase is:
- `B_n ≡ 3 (mod 5)` if `n≡1 (mod 4)`, and `B_n ≡2 (mod 5)` if `n≡3 (mod 4)`;
- hence `a_n≡0` or `4 (mod 5)), respectively;
- `2k_n ≡ -B_n-3n (mod 5)`, so the first phases are:

| n | a_n mod 5 | k_n mod 5 | (a_n+k_n) mod 5 |
|---:|---:|---:|---:|
| 1 | 0 | 2 | 2 |
| 3 | 4 | 2 | 1 |
| 5 | 0 | 1 | 1 |
| 7 | 4 | 1 | 0 |
| 9 | 0 | 0 | 0 |
| 11 | 4 | 0 | 4 |
| 13 | 0 | 4 | 4 |
| 15 | 4 | 4 | 3 |
| 17 | 0 | 3 | 3 |
| 19 | 4 | 3 | 2 |

This mod-5 table alone does not eliminate any depth; it is a reusable phase constraint to combine with the 2-adic and mod-4 source gates.

I also checked narrow exact subfamilies:
- For n=1 and s≡3 (mod 8), the high-bounce parent has a,k odd, k≥5, (a+k)≡4 (mod 16), and its oddodd-lowval parent has coordinate sum 2 (mod 4). Thus oddodd_lowval_blank_reach_iff followed by blank_section_odd_image excludes this n=1 competitor.
- For n=3 and s≡1 (mod 8), the high-bounce parent has k odd≥5 and (a+k)≡2 (mod 4), so blank_no_odd_sum_two excludes it directly.
- For n=3 and s≡5 (mod 32), the high-bounce parent meets the oddodd-lowval gate and its oddodd parent has sum 1 (mod 4), so blank_section_odd_image excludes it.

These are arithmetic subfamily checks, not yet Lean proofs. They do not close R0(s): other odd depths remain when v2(M) is large, and the n=1/n=3 gates leave other s-residues open. I have not promoted them as a theorem. The most promising next step is to formalize the reusable mod-5 phase lemma and one of the exact subfamily gates, then determine whether the R1 residual's mod16 split can be closed.
