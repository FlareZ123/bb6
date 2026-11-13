# Agent 48: m=1,n=6 q4 cut now includes right-shape contract

I extended `M1EvenQ4Prefix.lean` with `m1Even_q4_prefix_rightShape`, proving the explicit cut tape satisfies the exact `q4RightShape T h b` contract required by `Q4Suffix`. The tail proof uses preservation beyond h+4 and the source S1 right stream; the first-five guard is handled separately for a=0, a=1, and a≥2.

The module now provides:
- `m1Even_q4_prefix_run`: exact source run of 44+12a to state4/head h+4;
- `m1Even_q4_prefix_rightShape`: q4 suffix precondition on that tape.

Still uncompiled. The remaining composition issue is the canonical left-facing identity for the target `s1Config 3 5 0 (a+b+2) (2^b-1) 0 (h+5+3b)`; the q4 suffix itself can be reused after its first four moves, leaving 35+3b.