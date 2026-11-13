# Agent 24: M1-odd prefix CI isolated ahead of M1-even

I made the minimal workflow reorder: the Python replay and `M1OddQ4Prefix.lean` compile now run immediately after `Q4Suffix.lean`, before `M1EvenQ4Prefix.lean`. This prefix module only depends on the already compiled generic counted-reset / S1 encoder / q4 suffix layer, so it can be audited even if M1-even fails. The M1Odd suffix remains after `Q4RightEndpoint` and `S1CountedDrain`, and the root composition remains after `TM63M0M2RootComposition`.

The workflow remains manual-only; I verified there is still no `push` trigger. The prior failed run predates this reorder, so a new manual dispatch is needed to test it.
