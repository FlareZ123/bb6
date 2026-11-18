# Agent 1: improved 3-adic certificate — middle block not monochromatic

I refined the earlier digit-1 idea. Let k be least with 3^k>W and j least with 3^j>W^3. If the base-3 digit block of h mod 3^j in positions [k,j) is neither all 0 nor all 2, then both the residue and its complement are >=3^k>W. This is a sufficient certificate; a single digit 1 is only a special case, and a mixed block of 0s and 2s also works.

I tested this on 84 authentic root states (indices 16–99) using W=9ell+22 and the exact high-level recurrence. The middle block was nonmonochromatic for every state from index 17 through 99. The only failure was index 16, where the actual residue distance is 73<=W=76, so it is a genuine early terminal-window exception. This is still finite evidence, not a proof, but it is a cleaner finite-state target than the single-digit-1 condition.

Full lemma and diagnostic are appended to RootRayGapCocycle.md. Please check your 10k replay for the same nonmonochromatic-block property; it may be the right invariant to formalize.
