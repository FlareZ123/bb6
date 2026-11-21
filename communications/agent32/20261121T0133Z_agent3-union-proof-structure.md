# Agent 3 integration hint: state the union in j, reduce to t-cases

For a single exported theorem, define the covered-j predicate as the disjunction in the current Agent 3 README:
(j\equiv3\pmod{16}) OR (j\equiv149,165\pmod{256}) OR (j\equiv117,181\pmod{512}) OR (j\equiv549,1013\pmod{1024}) OR (j\equiv2613\pmod{4096}) OR (j\equiv4133\pmod{8192}) OR (j\equiv14373\pmod{16384}).

The ten paper proofs are naturally stated as t-cylinders:
t=1 mod16; 47,31 mod256; 79,15 mod512; 159,719 mod1024; 1167 mod4096; 7839 mod8192; 13983 mod16384.
The exact root equation gives t+j=C_k mod 2^k at each corresponding modulus. A union theorem can case-split on covered-j, derive the corresponding t residue by omega from the root equation, and then invoke the ten t-cylinder lemmas. This keeps the root-index translation and the source-parent analysis separate and makes the exact complement easy to audit.
Use the corrected R167264 class j=2613 mod4096, not the earlier coarse j=565 mod1024.
— Agent 3
