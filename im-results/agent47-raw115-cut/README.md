# raw115 candidate closure

**Status: complete candidate partition, not yet a source-accepted cylinder closure.**
Parent: `1RB---_1RC---_0RD---_1LD1RE_---0RD_------`. It has six holes. The target is the weighted first-one bound 7014, not an assertion of BB(6).

The existing raw99 enumerator (1000 primitive steps, cycle window 256) produced 6,706 splits, 117,987 cycle leaves, 28,643 last-hole leaves and 7,609 open leaves. Physical mass: cycles 226,257,075; halt 15,735,093; last-slot ordinary completions 687,432; open 1,461,025. Total 244,140,625 = 25^6. Maximum observed weighted halt score 458. These counts are untrusted discovery data until the source checker accepts them.

FAR search against the existing raw114 DFA bank and canonical DFAs through size four covered 7,472 open leaves; 137 remained (mass 4,625). The selected 37 DFA codes are retained in far-bank.txt. The existing single-sweep discovery found 127/137 candidates. The ten remaining tables are hard.txt (zero-based IDs). Sparse n-gram search closed candidate IDs 0,1,7,8 at widths 6,5,17,3 respectively, with state counts 1344,243,3405,160 and left/right edge counts (128,13),(35,17),(135,855),(9,16).

The remaining six candidates have explicit symbolic counter-return constructions below. No positive candidate is a theorem until original-source Lean accepts its certificate.

## Counter return mechanism

Words are nearest-first, as in Agent31Pump.Z0: the left word includes the scanned cell, the right word excludes it. Write D(a,b,X) for state D, left word 00(1010)^a(11)^b X, empty right word. For hard IDs 2,3,4,5,6 the common transfer is

    D(a,b+1,X) -> D(a+1,b,X), cost 14+8*a.

The proof uses arbitrary untouched suffix X; with a=0 it is a fixed 14-step trace. For a=n+1 it is a fixed prefix, two arbitrary-repeat sweeps, and fixed suffix. In particular the transfer does not depend on b.

Reset macros, expressed at positive a, are:

| ID | Input a | X | Output b | Cost |
|---|---|---|---|---|
| 2 | 3n+1 | empty | 6n+4 | 27+32n |
| 3 | 3n+1 | empty | 6n+4 | 21+24n |
| 4 | n+1 | empty | 2n+4 | 21+8n |
| 5 | n+1 | 1 | 2n+5 | 26+8n |
| 6 | n+1 | 1 | 2n+6 | 49+16n |

Every output has a=0 and preserves X. Starting from a=0, drain b into a by repeated transfers and then reset. IDs 2/3 start with b=1 and preserve b≡1 mod 3, since b' = 2b+2. ID4 starts b=1 and needs only positivity. IDs5/6 start b=5 and b=4. Blank entry steps are 3 for IDs2/3/4, 58 for ID5, 39 for ID6.

ID9 uses B(a,b) with state B, left word 0(111111)^(a+1)(01)^b and empty right word. Transfer B(a,b+1) -> B(a+1,b) costs 32+12a; reset B(a,0) -> B(0,3a+6) costs 121+36a. Authentic blank entry B(0,1) at step 50. Draining and resetting gives b'=3b+6. Every macro has positive cost. Hence if these symbolic equations are accepted, the six machines are nonhalting for all compatible completions by unbounded iteration. These are inductive candidates rather than finite extrapolation.

## Reproducibility

Use agent2-tnf-raw99/enumerate.cpp, agent47-raw114-cut/seeded_far.cpp, agent31-three-hole-tnf/generate_sweeps.py, agent47-raw114-cut/multi_sweep.py, and the existing sparse n-gram checker. Discovery hashes (SHA256, newline-terminated):

- open.txt: 473e54afdb33cc1d8e1cca38c9b8a2dcdedd7fe8c9ad2898847b515c11c36b7e
- unresolved.txt after FAR: 72ffb4e99a888caacd9cca27bc619df6a515b3fe799996cdc0a70d9f6c80f6d6
- hard.txt: b8f3a0680278d0bdea0e45b8339d7497ec1d1d912f5bd4c34d84e70a0bf99aed

Next: generate the six counter proofs using SweepPumping, produce checked leaf certificates for all candidates, and graft the resulting weighted cylinder theorem into the canonical roster only after original-source Lean acceptance.
