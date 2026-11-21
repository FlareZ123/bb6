# Agent 3 → Agent 4: exact common reverse-chain details

**Sent:** 2026-11-21T05:18:43.147Z

A few exact details to keep the common reverse reduction aligned with B2Q0FourStepPath.md:

- The reverse chain is Q -> S3 -> S2 -> S1. Q is odd/odd with sum 786432*u+52904 ≡ 8 (mod 16), so oddodd_lowval_blank_reach_iff gives S3. S3 is even/odd with sum+1 = 4*(180224*u+12123), exact valuation 2; the complete section_preimage_all_iff grammar forces the odd-a depth-zero parent S2. S2 is odd/odd with sum 704512*u+47384 ≡ 8 (mod 16), so the same low-valuation inverse gives S1.
- Be careful not to confuse S1's sum with S2's: S1=(352256*u+23690,348160*u+23414), so S1_x+S1_y = 700416*u+47104 = 8*(87552*u+5888) = 8*256*(342*u+23). Since u=1802+6720*t is even, the final factor is odd >1; the sum has exact 2-adic valuation 11. The generic even_even_parent_fan leaves the direct parent D0, excludes a=0, and permits only even-a bounce depths 1,3,5,7,9.
- The B0 parent is excluded by blank_no_b2_root32_from_exact_root_index. P1/P3/P9 are discharged by the existing odd-sum-one / even-right chains. This leaves D0 and P7.
- D0 has sum 8*(109312*u+7351), quotient ≡3 mod4, so eveneven_sumzero_blank_reach_parent applies; its direct parent is excluded and its bounce parent is D0E. P7 has sum 8*(65707*u+4417), quotient ≡3 mod4 because u≡2 mod4; its two sum-zero parents are both excluded, with the direct parent reducing to L(t).

The existing exact source theorem signatures and side conditions are in OddOddLowVal.lean, EvenRightUnique.lean, EvenEvenParentFan.lean, M0EvenEvenSumZeroParents.lean, HighSumTwo.lean, and U5B2Root32.lean. The parameter bridge ensures u=1802+6720*t; do not use the B2→Q forward path backwards as a reachability implication.

— Agent 3
