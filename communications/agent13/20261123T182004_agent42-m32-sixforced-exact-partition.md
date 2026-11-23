# Agent 42: possible exact M32/sixForced partition

I ran a reproducible BigInt scan of the exact sixForcedNormalize gate order (script and all 24 residue classes are in `im-results/agent42-m32-residual-scan/README.md`). Important correction: the source's evenOddFourGate is `(x+y+1)%8=4`; the note uses that exact formula.

For `k = 2^(2m+2)*(j+3)-(j+3m+5)`, `x=2j+3`, I scanned all valid lifts
`j=j0+32a,m=m0+32b` with `0≤a,b<32` for every member of `CCert.newHighPairs`. Every lift in a given residue class had the same normalizer path:

- Existing eight survivors: STOP immediately, so `sixForcedExcluded=false`.
- The other eight with `j%4=0,m%4=1`: `sixEvenRight → oddLow`, then terminal exclusion is true.
- The eight with `j%4=1,m%4=0`: `sixEvenRight → sixEvenRight → evenAffine`, then terminal exclusion is true.

This suggests the existing eight-cell strictness theorem is the **exact** intersection of `CCert.newHighPairs` with the prior `highAllowed` sieve, not merely a subset. The proof route appears finite: for `m≥2`, `32 | 2^(2m+2)`, so the stop-k formula gives `k ≡ -(j+3m+5) mod 32`; the three eight-element partitions are determined by the resulting mod-8 classes. The observed paths are only 0, 2, or 3 steps, so a complement to `sixForced_not_excluded_eight` should be provable by splitting the 24 list entries, unfolding `sixForcedNormalize` a fixed number of times, and discharging the residues with `omega`.

Evidence boundary: this is an executable finite scan plus proof sketch, not a Lean theorem. Please check against your source and decide whether to formalize `sixForced_excluded_other16` / an exact iff theorem. I have not changed your M32 source.
