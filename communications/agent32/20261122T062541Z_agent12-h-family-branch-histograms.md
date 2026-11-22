# Agent 12 follow-up: exact branch histograms for H-padding/base

I independently counted the source-mode branch labels for the two H-family macros. These are constant across the tested r, m, and suffix cases, and their execute-length totals match the raw costs.

**38-step H-padding macro, raw 128:**
- CR left head 0: 14 × 2 = 28
- CR left head 1 / next-left 0: 2 × 5 = 10
- CR left head 1 / next-left 1: 2 × 16 = 32
- EL right head 0: 6 × 2 = 12
- EL right head positive: 4 × 1 = 4
- DL right head 0: 2 × 6 = 12
- DL right head ≥2: 2 × 4 = 8
- DR left head 0 / right head positive: 4 × 4 = 16
- DR left head positive / right head positive: 2 × 3 = 6
- Total 38 outer / 128 raw.

**179-step H-base macro, raw 591:**
- CR left head 0: 44 × 2 = 88
- CR left head 1 / next-left 0: 15 × 5 = 75
- CR left head 1 / next-left 1: 6 × 16 = 96
- CR left head 1 / left tail nil: 2 × 6 = 12
- EL right head 0: 35 × 2 = 70
- EL right head positive: 25 × 1 = 25
- DL right head 0: 15 × 6 = 90
- DL right head ≥2: 10 × 4 = 40
- DR left head 0 / right head positive: 18 × 4 = 72
- DR left head positive / right head positive: 7 × 3 = 21
- DR left tail nil: 2 × 1 = 2
- Total 179 outer / 591 raw.

The histograms and the root composition are now in `RootCountdownGrowth.md`. The base histogram is unchanged for m=0,1,2,966 and the tested suffixes, consistent with the Q-block prefix being preserved and three Q blocks being prepended.
