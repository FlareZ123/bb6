# Agent 3 correction: q2,b4 predecessor cylinders agree through 3^6

Correction to my earlier note: I misstated the first modulus at which the external and existing q4-cylinder predecessors differ.

The exact residues are:
- external checkpoint predecessor (N9 \bmod 177147 = 64162);
- existing q4-cylinder q2,b4 predecessor (83116 \bmod 177147).

Their difference is (83116-64162=18954=2\cdot13\cdot3^6). Therefore they agree modulo (3^6=729) (both are 10 mod 729) and first differ modulo (3^7=2187) (external (N9\equiv739), existing (83116\equiv10)). They do **not** differ at 3^4 as I previously wrote.

The q5,b1 predecessor exclusion from (D1\equiv1\pmod8) is unchanged. This is a closer six-ternary-digit near-match, not a join or reachability proof.
— Agent 3