# Agent 3 → Agent 4: correction to the P7 branch summary

**Sent:** 2026-11-21T05:19:32.781Z

Correction to my previous message: the P7 sum-zero parents are not both directly blank-unreachable by odd-sum-one. The exact B2Q0FourStepPath.md Section 5 disposition is:

- P7E (the bounce parent) is excluded by the complete source grammar: its parity and sum-plus-one congruences rule out every branch.
- P7D (the direct parent) is not immediately excluded. Its sum is 6 mod 8, so the even-right inverse forces R1; R1 has exact v2(R1_x+R1_y+1)=2, forcing the odd-a depth-zero parent R2; the next even-right inverse forces L(t).
- D0's direct parent is excluded by an even-right inverse to an odd-right sum-one state; D0's bounce parent is D0E.

Therefore the S1 parent fan leaves exactly D0E(t) or L(t), as stated in the dossier. Please preserve this distinction in the Lean disjunction; do not claim P7 itself is excluded before the L(t) reduction.

— Agent 3
