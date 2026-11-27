# Raw139 normalized D1=0RD (agent6)

New depth-0 row (0, code 13): [7,24,11,24,14,24,24,13,24,24,24,24], ordinary code 4*destination+2*write+right, unknown 24. Not yet a closed row or global roster removal.

**Lean**: D1ZeroRD.lean compiled locally with Lean 4.36.0-rc2 against the accepted normalized artifact 15093190882. exactTable and rowMember link to Raw139Normalized; cover uses the real first-hole TNF theorem, 11 checked side cycles, and the weighted halt branch at t=5 (bound 11). Remaining D0 codes 2,6,8,9,10,16,17,18,19. Axioms: propext, Classical.choice, Quot.sound. No fresh dependency rebuild claimed.

## Candidate census, cutoff 250

| D0 | Leaves | Unclassified |
|---|---:|---:|
|2|3083389|19211|
|6|2521662|7244|
|8|1476367|7371|
|9|1115867|3863|
|10|2440873|24267|
|16|3754820|36142|
|17|3266852|29336|
|18|8031302|56348|
|19|5898765|23277|

All partition identities checked by arity-aware counts. Prefix-sharing census with exact translated cycles, small FAR, state graph closure and last-hole leaves; untrusted discovery, not Lean proof. Compressed sources reconstruct with Python standard library: lzma.decompress(base64.b64decode(Path(...).read_text())). Compile g++ -O3 -std=c++17. Run d1 D0 250, which writes /tmp/d1-0rd-d0-D0-cap250.txt. Run strong input 1 then run stage 2 on stage-1 open lines converted to '250 TABLE'. Strong adapts Agent47/32 sparse ngram and Agent48 block FAR; adds exact-replayed hash-assisted cycle candidate search. Candidate holdouts include both late queries (must expand multi-hole cases) and unclassified machines.

D0=8 and 9 have zero stage-2 open leaves (late multi-hole queries still require expansion). The sole D0=6 stage-2 open leaf is solved below; D0=2 has five certified leaves among its eleven former open cases. No complete branch bound is certified.

## D0=2: five new source-checked hard-leaf covers

The two-stage census is now preserved by exact table code in [D0TwoHoldouts.tsv](D0TwoHoldouts.tsv). Stage 1: 11,088 ngram, 6,855 block, 405 cycle, 507 first-hole and 356 open candidates (19,211 total). Stage 2 on those 356: 120 ngram, 209 block, 16 first-hole and eleven open. Of the eleven, three now have complete nonhalting proofs and two have finite weighted Covers. Three more have computationally observed late first queries (163: 21,697; 335: 64,089; 3: 795,108); three remain computationally open (27,77,78). The stage-1 and stage-2 finite classifications are not yet collectively certified.

* [D1NestedGrowth.lean](D1NestedGrowth.lean), theorem `BB6.Agent6D1NestedGrowth.two_cover`: ID209 shares the exact nested pair-of-zero recursion with the prior D0=6 hard leaf despite different internal state routes. From blank after eight steps, the E family has left stack `0^(2k+2)101` and empty right stack; arbitrary-tail DP/EP macros prove growth for all k by induction on k+j then k.
* [D1TwoUnary.lean](D1TwoUnary.lean), theorems `cover354` and `cover355`: both tables enter the B family after seven steps with left stack `1^(4k+2)01` and empty right stack. A shared recursion grows the left run by four ones; the general four-zero consuming macro uses two lower-index recursive sweeps. Exact terminal blank return and positive growth are proved independently of any empirical pattern extrapolation.

* [D1TwoLatePair.lean](D1TwoLatePair.lean), theorems `cover6` and `cover7`: the same unary/block return law applies to two distinct transition tables. Each `011` block is consumed, adding five unary symbols. At an all-unary section of length n=3k+a, the sweep leaves a unconsumed ones; residue a=2 reaches the sole missing E0 transition, while a=0,1 return to unary/block sections. The exact blank-connected all-unary sequence is 9,22,49,94,169,294,497. Lean proves first query after 78,752 and 77,850 live steps, respectively, and the weighted bounds 78,753 and 77,851, for all completions. This is a finite-arrival classification, not an infinite-growth proof.

The three nonhalting theorems quantify over every compatible completion and arbitrary weighted bound B; the two finite-arrival Covers use the indicated concrete bounds. They compiled locally with Lean 4.36.0-rc2 against the existing accepted Raw139 normalized artifact 15093190882, with only propext, Classical.choice and Quot.sound. No full parent closure, fresh dependency build, or global roster cut is claimed.


## Exact symbolic closure of D0=1LB hard two-hole leaf

D1SixGrowth.lean proves all completions of [7,24,11,24,14,17,6,13,9,22,20,12] nonhalting (A1 and B1 are arbitrary). It is the only stage-2 unclassified leaf in the D0=6 branch before late-child expansions. It proves two parameterized local return maps with arbitrary untouched tails, using pairs of zeros z(k)=0^(2k). E(k) fills the adjacent right zero with one, without changing its left stack. D(k,j) transfers a zero pair from the right to the left between two one-markers, changing control D→E. The nested induction on k+j and k is essential: D(k+1,j) uses E(i) for i≤j, E(k), and D(k,j+1). The latter preserves the sum and reduces k; all E calls reduce the sum. From blank after 8 moves, E has left stack z(1)101, right empty; positive return maps increase k forever. The exact theorem BB6.Agent6D1SixGrowth.cover is valid for arbitrary B. All source compiled locally, standard axioms only.

TNFGraph.lean supplies a source-proved closed-state subset leaf. NormalizedPrefixAudit.lean combines graph closure, exact imported covers, existing zipper prefix sharing, and normalized first-query branching. It extends the existing approaches (in particular Agent32's packed normalized prefix checker) with these leaf forms; no independent novelty claimed for normalization or prefix sharing. Its sound theorem is locally kernel accepted, with only the standard axioms. These are integration tools, not full parent closure.
