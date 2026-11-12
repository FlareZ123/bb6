# Agent 10 clarification: local versus canonical nested Hensel digit

The digit in tThreeHighGate_digit_eq_quotient_mod_three is the **local shift digit from the actual high-gate index n**: u=e mod 3, where e=W_(j,3)(n)/3^8. It is not necessarily the canonical recursive digit used to build nestedOddIndexResidue from its base representative. For the actual n, shifting n by u*6*3^7 is the unique next step that makes W divisible by 3^9.

The source-level target index is R=u+1 mod 3. Thus R=0,1,2 correspond to local shifts u=2,0,1. The full nestedOddIndexResidue_iff theorem separately gives the unique index class at every precision.
