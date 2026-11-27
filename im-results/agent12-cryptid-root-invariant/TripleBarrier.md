# Triple-one barrier (source proof development, November 27)

This is a prepared-state obstruction, not a claim of authentic #85 or #490 reachability. Pair symbols below are first coordinates (second coordinates zero); other tails can have arbitrary pairs. Source pin google-deepmind/cryptids 3647718b5df22e1a61462dec0376bd204526285a.

## New prepared halting families

- G(M,U)=CR([0],0^M U), M≥1. Initial corridor enters EL(0^(M+2)1,U) at cost 2M+23.
- EL(0L,[1,1,1]) halts in 67 steps. EL(00L,[1,0,1,1]) halts in 115 steps. Any earlier binary prefix can be scanned by EL: 0 costs 2, 1 costs 7, and puts the corresponding pair just behind the head zero. In particular [01]*111 and [01]*01011 are uniformly fatal.
- CR(111L,[a+2]R) halts in 43 steps, arbitrary a≥0 and tails. For a=0 use the token corridor; for a>0 reach CR(2L,0^4[a-1]R) after 41 and halt after 2. The general source lemma a12CR_triple_positive (TripleZeroSuffix.append.lean) reported standard axioms in CI 45976417248; the overall module failed in an independent tape-encoding lemma in SuffixHazards. With a trailing zero block, EL scans all zeros, then CR collects them into a right head 2(g+1); hence [01]*1110* is fatal. Source a12G_binary_111_zeros_halts in same run also reported standard axioms.
- CR(111L,0^n[a+2]R) with n≥1 halts in 43+6n steps. Reason: CR(111L,R0) -> EL(003L,R0) at 25; transfer n zeros at 2n; EL-positive initiates ordinary DR (head≥3) or token DR (head2) at 5; DR transfers n+2 zeros at 4(n+2), then consumes one from the 3 marker at 3, exposing a fatal 2 in CR, and halts at 2.
- Collectable prefix P=(0|10)* on CR-left, before 111L, with right shape either [a+2]R or 0[a+2]R, is fatal. CR-zero consumes a 0, increases right head by2. CR-one-zero consumes 10, increases right head by3 and prepends 0. Both preserve the stated right shape. Induct on P. Consequently any binary suffix of the form w 111 v where reverse(v)∈(0|10)* is fatal: the EL binary scan reverses v onto the CR stack, CR removes the initial zero to create right [2], then applies the collectable-prefix theorem. In forward order v∈(0|01)*, i.e. each trailing one is paired with a preceding zero. This strictly extends w1110*. Formal source attempt TripleIsolatedTail.append.lean (latest 4fde3bc4), pending CI; no full-kernel acceptance claimed.

## Scope

Exhaustive conditional source-transcription scan of all 2047 binary words starting with 1 through length11, at G(5,w), yielded 1362 halting cases, and every word containing 111 halted. That finite observation suggests a still larger language but **does not prove arbitrary triple containment**, especially where consecutive trailing ones are present. No observed root suffix need satisfy these languages. Do not conclude either authentic root halts.

The mathematical frontier is the authentic-root constraint or reachability of a fatal cylinder, not a longer forward scan (external work has already run >2.7M F sections). Use the exact arithmetic return map and this obstruction to reason about reachable suffix languages; do not treat a prepared configuration as a new BB(6) lower bound.
