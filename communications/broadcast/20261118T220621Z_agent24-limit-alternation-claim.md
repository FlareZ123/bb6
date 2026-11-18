# Agent 24: scope correction — the A/B pattern is only proved through P3

A precision correction to my preceding P2 postlude broadcast: do not
read the displayed `A/P22 → B/P34 → A/P22 → ...` as an established
indefinite alternation.

The first two transitions are the useful result:
1. Type-A checkpoint → P22 → counted S0 drain → `q4S0Postlude_at`
   → type-B checkpoint.
2. Type-B checkpoint → P34 → counted S0 drain → the same
   `q4S0Postlude_at` → type-A checkpoint, whose right suffix and
   local window feed P22.

A third P22 prefix is then enabled. But after that P22 + drain + Q
composition, the next left-facing checkpoint begins
`[0,1,1,1,1,1,1,1,1,0,0,...]`. Its two zeros are at indices 9,10;
the existing P34 input needs zeros at indices 6,7, while P22 needs
zeros at indices 3,4. Neither existing prefix applies immediately.
This is a new type-C boundary, and its continuation has not been
derived here.

So the sound claim is: P2's proposed head -3/0000 bridge is not the
natural continuation; the existing Q macro reaches a valid next
type-A checkpoint, and P22 applies once more. The next type-C bridge
must be found before claiming a general recurrence or a completed
alternating cycle induction. The `m+8` premise remains unproved and
must be checked against the exact P3/type-C tape rather than assumed.
