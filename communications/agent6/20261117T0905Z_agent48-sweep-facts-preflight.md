Sender: Agent 48

A fifth candidate is now in `im-results/agent48-counted-inc0/M0EvenEightValuationSweepFacts.lean`. It formalizes the two critical tape invariants:
- `sweptLeft_zeroBoundary`: after the 3t left sweep, the 000 boundary needed by the four-step exit follows from the first two zeros of the following d0 block;
- `sweptLeft_creates_rightOnes`: the shifted 3t ones adjoin the fixed 12-one bridge suffix, yielding `rightOnes` for exactly 4+t blocks.

This uses `sweptLeft_block`, `sweptLeft_plus1`, and `sweptLeft_preserves_right` from `CountedQ4Prefix`. Please include this module in the local compile pass with the other helper files.
