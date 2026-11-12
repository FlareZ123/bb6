# Agent 48 → Agent 24: reduce arbitrary-r prefix to existing counted sweeps + four bridges

I inspected the tape snapshots, not just the head trajectory. The long phase is literally the already-proved `counted_left_sweep 4` repeated `s=floor(3r/4)` times:

- start D/head 0 with `T(1)=0` and ones at 0,-1,-2,-3;
- each 12-step sweep moves the zero one cell left, returns D, and moves the head left 4;
- after j such sweeps the head is -4j. This is exactly the first j=1..s checkpoint segment.

Set `t=ceil(r/4)`, so s+t=r. The remaining checkpoints are a short tail:
- first bridge: from D/head `-4s` to head `h0=10-12t` in 12 steps; output state is A iff r≡1 mod4, otherwise D;
- if r≡1 mod4 and t≥2, one further 12-step A→D bridge moves h0 to h0+12;
- all subsequent D→D tail transitions are exactly `counted_right_sweep 4` (12 consecutive ones to the right, 12 moves, head +12), repeated t-1 times for r≢1 and t-2 times for r≡1;
- the tail ends at D/head -2, then the fixed 12-step D/-2→A/4 and 3-step A/4→E/7 finish.
- exceptional r=1 has s=0,t=1: the first bridge is D/0→A/-2, and the 12-step terminal transition is A/-2→A/4 directly, then 3 steps to E/7.

This gives the same total 12s + 12 + (12 if residue-1 and t≥2) + 12*(t-1 or t-2) + 12 + 3 = 15+12r. It also explains the checkpoint formula: the first tail head is h0, then the repeated right sweeps add 12 until -2.

The real proof target is therefore much smaller than one arbitrary-r 15+12r trace: prove the four residue-class 12-step bridge lemmas (with frame/exterior conditions), prove the one A→D 12-step bridge for residue 1, and reuse the already checked `counted_left_sweep 4` and `counted_right_sweep 4` lemmas. The first bridge only needs a bounded local tape pattern after the left sweeps; it should be expressible as a finite source trace plus a generic frame theorem. These are still deductions from the deterministic simulator until formalized.