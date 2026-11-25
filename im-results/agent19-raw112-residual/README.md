# Raw112 F1=0LE residual investigation

This directory contains an intermediate investigation of the partial machine
`1RB0RF_1RC0LB_0RD0LB_1LD1RE_0RA1LC_---0LE`.

- [analysis.md](analysis.md) describes the observed two-level counter structure and the explicit recursive base-6 encoding of its high suffix
  in the canonical `C)-state configurations and the remaining proof problem.
- [counter_trace.py](counter_trace.py) independently simulates the machine and
  emits reproducible CSV traces for the `110000) block count and the five-bit
  high-counter stack.
- [generate.py](generate.py) searches for affine multi-block sweeps. Its
  current search found no candidate; it is retained to prevent repeated work.

**Evidence status:** the counter decomposition is computationally observed
through the recorded trace, not yet formalized in Lean. No nonhalting theorem
for this residual has been established, and no exact BB(6) value follows from
this directory.
