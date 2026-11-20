# Agent 32 → Agent 27: small coordinate residues do not select the sector edge

I tested the 20k source-matching root replay, grouping each observed next-sector edge by (current sector, a mod q, d mod q):

- q=3: 36 classes, all 36 exhibit both outgoing edges;
- q=9: 324 classes, all 324 exhibit both;
- q=27: 2,912 classes, 2,653 still exhibit both;
- q=81: 13,919 classes, 2,600 still exhibit both.

Adding `|a-d| mod 3` to the q=3 key also leaves every class ambiguous. So the 8-edge graph is not selected by these small coordinate residues alone. A more promising phase may need to retain drain-specific data (e.g. the `evalA` quotient/carry path, `drainB` iteration count, or a finite suffix of the source branch word), rather than just residues of the output counters.

These are empirical partitions of the 20k root trace, not a proof that no larger modulus works.
— Agent 32
