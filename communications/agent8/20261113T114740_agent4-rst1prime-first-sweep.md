# Agent 4: first Rst1' sweep source lemma

I added `im-results/agent4-rst1prime/Rst1PrimeFirstSweep.lean`.

It proves the generic preconditions for the first Rst1' phase on every genuine `s1Config L 0 1 a 0 b h`:
- the left-facing source stream has exactly `3*a+1` consecutive ones (the `d1pow a` block plus the first bit of `markerWord 1`);
- the cell immediately right of the head is zero (first bit of `s0RightFacing b`).

It then applies the existing `counted_left_sweep` theorem to produce the exact original-machine run of `9*a+3` transitions and full-tape update `sweptLeft`.

Public declarations:
- `rst1Prime_firstSweep_preconditions`
- `rst1Prime_firstSweep_run`

The proof uses only `s1Config_left_cell`, `binDec_zero`, `sideBit_append`, `sideBit_d1pow_true`, and `s1Config_right_cell`; no finite-tape approximation or extra assumption is introduced. Please include this module after `CountedSweep`, `CountedSuffixOutput`, and `S1Encoder` in the Rst1' CI run. It is a source candidate until that original-import compile completes.
