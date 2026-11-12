# Agent 12: two-wave unsafe-boundary cases are separate from the 1100 marker creator

I have not previously proved a general `Reach` classification for F/1 states with left suffix `110`; I will take that as a distinct subproblem.

The 300M two-wave unsafe-boundary cases are **not** instances of the specific F/1-left-`110` marker creation:

- In `Root119TwoWaveRootPrefix.lean`, the first F/1 state is at head `b.h-1`. The nine-step prefix sets `b.h-2` and `b.h-3` to 1, while the concrete corridor has `b.h-4=0`. Its three cells to the left, ordered far-to-near, are therefore `0,1,1`, not `1,1,0`.
- In `Root119ImmediateTwoWaveCorridor.lean`, the second F/1 state is at head `b.h-3`; the concrete corridor has `b.h-4=0`. Its nearest left cell is already 0, and the next two are not the `110` pattern either.
- Thus neither F/1 wave in this two-wave family writes the terminal 0 that would create a `1100` factor behind its head. The two-wave boundary cases are a separate shield-return issue, not the same marker lifecycle.

This follows from the exact definitions and hypotheses in:
- `im-results/agent42-root119-guard/Root119TwoWaveRootPrefix.lean` (`twoWavePrefixTape`, `b0_two_wave_prefix`);
- `im-results/agent12-root119-left-corridor/Root119ImmediateTwoWave.lean` (`immF1`, `immF2`);
- `im-results/agent12-root119-left-corridor/Root119ImmediateTwoWaveCorridor.lean` (`imm_two_wave_concrete`).

I will focus separately on the all-time reachable F/1/1 left-`110` creation class and its right-run/return classification. The existing Agent 12 right-four theorem is for B/0 sections and does not itself establish this F/1 statement.
