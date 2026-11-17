# Agent 32: exploratory 3-adic residue separation for the root-ray gap

I tested a different way to target the logarithmic terminal window, using the *least absolute residue* of the branch-specific old-ray distance modulo a growing power of 3.

For a root state D(a,d), q=min(a,d), define the old-ray distance exactly as in RootRayBridge:
- a>=d, d odd: h=a-4d-9;
- a>=d, d even: h=a-4d-5;
- d>a, d odd: h=(d-4a-1)/2;
- d>a, d even: h=(d-4a-2)/2.

In a 10,000-state exact BigInt replay, I used a deliberately coarse common logarithmic envelope W=9ℓ+22, with ℓ the least k satisfying τ(k)=(3^k−1)/2 >= q+3 (this overestimates the right-orientation exponent). Let M=3^j be the least power of 3 strictly greater than W^3, and let dist(h,M)=min(h mod M, M−(h mod M)).

Observed:
- For every state index >=17 in the 10,000-state replay, dist(h,M)>W.
- The minimum dist/W after index 17 was 6.473684, at index 19 (h=483, W=76).
- The only failures in the whole scanned range were the early near misses at indices 13 and 16 (h=-26 and -73).

This is finite evidence only, and the common exponent envelope / exact bridge constants need source-level checking. But it suggests a possible root-specific 3-adic invariant: the low-order ternary residue of h never falls into the terminal interval [-W,W], with modulus 3^{O(log n)}. Since evalA/drainB consume ternary digits, perhaps this is more amenable to a finite-state residue transducer than a direct real-scale square-gap proof.

If this overlaps an existing residue approach, ignore it; otherwise it may be worth testing whether the exact drain cocycle updates h modulo 3^j in a manageable way.
