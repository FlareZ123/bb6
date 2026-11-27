# Exact far-prefix event skip across the tertiary countdown

**Status:** kernel-checked prefix independence and affine arithmetic; exact arbitrary-precision evaluation in C++, conditional on the tertiary primary cycle identity. This supplies a substantial initial protected suffix for the next secondary phase, but the remaining near-head cells are uncomputed. The full secondary countdown and F421 decision remain open.

## Autonomous far-prefix recurrence

Write B_i=2^i in far-to-near order and encode the first odd crossing's input by pairs (Q_i,P_(i-1)-1), with dummy second parameter 3 at i=0 and an extra final pair (b,P_last-1). One complete positive tertiary cycle consists of the normalized drain A, subtract one from each surviving first parameter, normalized drain B, and transform surviving rows (u,v) at scale B into (u-1+B,v-B), resetting the first second parameter to 3. Append the new leading-b ghost, computed from the two drain counts and merging carries.

Each normalized drain is a left-to-right fold in far-to-near order: later cells cannot affect earlier survivors. Thus a prefix chosen at any finite iteration can be evolved without further births, and the result is an exact prefix of the full list at every later iteration. In particular, its last first parameter is known, but the corresponding original P-run depends on the next row and is not known.

If every first parameter is at least 4B, both drains retain every row. The first parameter decreases by 3B and the second increases by B, apart from the dummy. If all first parameters are at least (3k+1)B, k successive cycles have this affine form. This proves the event-skip algorithm: advance to the next threshold, evaluate one actual deletion cycle, repeat. F421PrimaryEvents.lean proves iterPrefix and iterateAffine with standard axioms, independently of machine execution. These theorems are stated in A-input orientation; primary_events.cpp uses equivalent P/Q edge orientation.

## Exact authentic endpoint prefix

From the authentic odd-65700 seed, evaluate 70,000 complete primary cycles, obtaining 8,428 P/Q cells. Thereafter keep that prefix and the known leading-b ghost, and discard all future births. Jump to the end of the 2^8214-1 tertiary cycles using the exact event skip. There are 6,222 deletion events and 198 surviving known Q entries, of which 197 have known P. An independent Q-only implementation gave exactly the same 195 normalized non-fixed Q entries.

The following tertiary-zero crossing retains every tracked row in drain A; C restores their old P values and decreases Q_i by B_i exactly. For the next secondary count T=2^8215-1, all 197 known P satisfy P_i >= 2*B_i*T+3 and all 198 Q satisfy Q_i >= B_i+2. The first ten floor(P_i/(2*B_i*T)) are 19,5,68,74,11,1690,180,431,89,276. Some P-runs are not divisible by 2B; the protected-suffix inequality handles them. This does not imply the required divisibility or budget for the remaining near-head portion.

## Reproduce

Use the authenticated secondary-zero prefix-state.txt as in TertiaryEpoch.md, then:

```sh
python primary_events.py prepare
g++ -O3 -std=c++17 primary_events.cpp -lgmpxx -lgmp -o primary_events
./primary_events 70000 8214
python primary_events.py check
```

The input and output digests and full deterministic checks are in primary_events.py. The output is about 991 KB, omitted from Git as generated data. It starts with 0 0 (unknown global a,b) and its last P is 0 as an unknown sentinel, not a real zero-length cell. The proof of the finite arithmetic prefix uses the conditional tertiary cycle and source guard; original-machine composition remains separate.
