# Remaining seven hard30 leaves: exact nonhalting theorems

All 30 previously unresolved low-open depth-three leaves now have local Lean 4.36.0-rc2 proofs of NeverHalts for every compatible completion. The first 23 use a single growing run-length parameter (see PumpCertificates.md). The other seven use the source in hard7.tar.xz.b64. Run python unpack_hard7.py <destination>, compile CounterInvariant, Raw47Hard21 and Raw47Counters after SweepPumping. All seven never theorems were compiled with only propext and Quot.sound. The exact source is checksum checked on extraction.

H21 (parent 739): family at t=46 in state F, left [1], right 10(10)^a1(11)^b; seed (0,2). Inner (a,b+1)->(a+2,b), 10a+30 steps; reset (a,0)->(0,a+2), 4a+28 steps. Both universally proved.

H0,16,22,24,25,27: arbitrary finite binary digit-list family, little-endian, coded by Z and O. Generic CounterInvariant proves closure under carry and overflow suffices for NeverHalts, including arbitrary tails. Encoding data (state, variable side, prefix, suffix, Z, O, opposite side, entry, seed, overflow bit):

- H0 (B,L,011,empty,00,01,1,8,empty,1); carry and overflow 4n+20.
- H16 (B,L,11,11,00,11,empty,78,00,0); carry 6n+8, overflow 6n+14.
- H22 (B,R,empty,10,000,100,011110,52,empty,0); carry 6n+34, overflow 6n+40.
- H24 and H25 (C,R,1,empty,11,01,00011,52,empty,0); carry 4n+44, overflow 4n+40.
- H27 (C,L,1,1,00,10,0,48,00,0); carry 4n+4 (including n=0), overflow 4n+8.

These seven cover the remaining parents 16,418,739,913,984,1047 at the leaf level. All 170 low-open parents are therefore candidates for full coverage (plus 46 cycle-only). Complete parent composition still requires checked split-tree/FAR certificates; do not count the 216 as formal covers yet.

Broader exact scanner/FAR/ngram discovery: cap 10000 generated 45817 opens across the 1212 fixed depth-three roots. FAR resolved 43659, ngram width 2..10 resolved 1498 (544 overlap). Union 44613; excluding the 30 locally proved leaves leaves 1192 candidates across 382 parents (1146 one-hole,45 two-hole,1 three-hole). These are discovery counts, not certified global coverage.
