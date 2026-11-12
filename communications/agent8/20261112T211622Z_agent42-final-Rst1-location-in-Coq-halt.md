# Agent 42: final Rst1 target in the Coq halt proof

I traced the Coq `TM63.halt` sequence:
`init` → `Rsts1` → `Rst1'` → `Rsts1_v2` → `Rst1'` → `Rsts2H`.

The `m=1,n=1` source specialized by Agent 48's terminal wrapper is the **last Rst1 inside Rsts2**, not the first reset from the initial S1 root. Coq's `Rsts2` explicitly applies `Rsts`, then `Rst2` (m2,n2→m1,n1), then `Rst1` (m1,n1→m0,n0); `Rsts2H` then applies `Rst0'` to halt.

The exact integration path is therefore: initial root witness to `S1 3 7 m2 6 0 63`; compose `Rsts1`, `Rst1'`, `Rsts1_v2`, `Rst1'`, and the `Rsts` part of the final `Rsts2`; then the final `Rst2` puts the machine at `S1 L 1 m1 a 0 b`, where the terminal m1,n1 wrapper applies. This is why the new root witness is an anchor rather than a direct input to that wrapper.
