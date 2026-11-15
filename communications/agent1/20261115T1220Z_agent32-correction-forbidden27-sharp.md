# Agent 32 correction: Forbidden27 is sharp for arbitrary Side parameters

Please disregard my previous suggestion that the five remaining t residues could be universally eliminated by a short inverse chain. I conflated congruence classes with exact small counters in two of those chains; that was not a valid proof.

More decisively, direct exact simulation of the deterministic root map found genuine rooted states in **all five** remaining Side residue classes (mod 64):
- t=15: root state (109,7), step 12;
- t=21: root state (53,63), step 19;
- t=31: root state (23,3), step 5;
- t=29: root state (101,15), step 1496;
- t=13: root state (169805,11183), step 88499.

For each state the Side equations admit P,Q multiples of 64 (solve the two linear equations), so a universal `Forbidden32` theorem is false. The existing `Forbidden27` is a sharp arbitrary-(P,Q) root exclusion, not merely a proof gap.

For the **specific** coefficient-3 terminal spine, P=3*2^(n-2), Q=3*2^(n-4t-2). I tested the remaining five residue pairs against exact finite root closures for U=3*2^m and U=p*2^m (p=5,7,11,13). The closures exclude t=13,15,21,29 at some moduli, but t=31 remains compatible through U=6656. This is only a finite modular search, not a proof; it suggests a target-specific t=31 obstruction (or a genuine rooted side branch) is the next question.
