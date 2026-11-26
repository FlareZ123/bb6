# raw115 candidate closure

**Status: all 54 child proof cuts compiled and the complete parent theorem elaborated with standard axioms; strict original-source artifact assembly remains to be accepted.**
Parent: `1RB---_1RC---_0RD---_1LD1RE_---0RD_------`. It has six holes. The target is the weighted first-one bound 7014, not an assertion of BB(6).

The existing raw99 enumerator (1000 primitive steps, cycle window 256) produced 6,706 splits, 117,987 cycle leaves, 28,643 last-hole leaves and 7,609 open leaves. Physical mass: cycles 226,257,075; halt 15,735,093; last-slot ordinary completions 687,432; open 1,461,025. Total 244,140,625 = 25^6. Maximum observed weighted halt score 458. These counts are untrusted discovery data until the source checker accepts them.

FAR search against the existing raw114 DFA bank and canonical DFAs through size four covered 7,472 open leaves; 137 remained (mass 4,625). The selected 37 DFA codes are retained in far-bank.txt. The existing single-sweep discovery found 127/137 candidates. The ten remaining tables are hard.txt (zero-based IDs). Sparse n-gram search closed candidate IDs 0,1,7,8 at widths 6,5,17,3 respectively, with state counts 1344,243,3405,160 and left/right edge counts (128,13),(35,17),(135,855),(9,16).

The remaining six candidates have explicit symbolic counter-return constructions below. The source preflight and all 54 branch cuts have now succeeded across two runs; the final parent theorem already elaborated in the recovery assembly. The strict source/object closure acceptance remains separate, as explained below.

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

## Original-source proof recovery

The pinned producer revision is `496465aee626aaf2237367fb90888499692dc772`. [Run 45755928881](https://github.com/FlareZ123/bb6/actions/runs/45755928881) generated all 456 Lean source files and passed preflight. Exactly 53 of 54 branch jobs uploaded successful objects; only branch (17,12,18) was cancelled. [Run 45758827627](https://github.com/FlareZ123/bb6/actions/runs/45758827627) compiled all six missing child roots, producing artifact 15089595287. Its final assembly elaborated `BB6.Agent47Raw115.all_completions`, `sound`, and `residual_count` with axiom profiles [propext, Classical.choice, Quot.sound], but failed the source manifest because Raw115Sparse7Chunk00_0002.olean was missing.

The actual recovery ZIP and original generated-source ZIP show the error: Raw115Kid17_12 imports **Raw115Sparse8**, whose full source closure compiled in the successful repair job. That job did not use any of the extra generated Sparse7 chunk files it uploaded. Raw115Kid17_00 imports **Raw115Sparse7** and already compiled successfully in the original artifact 15088790393. Local inspection verified the archive hashes and all 57 shared object hashes between that original artifact and the repair artifact; every common object is byte-identical.

The existing manual recovery workflow now performs assembly only: [pinned archive and exact producer-closure recovery](../agent12-raw115-consumer/recover_raw115.py) uses the [55 immutable artifact pins](../agent12-raw115-consumer/recovery-pins.json), keeps the original source ZIP authoritative, refuses any differing duplicate object, checks every producer's complete transitive import cut against the final source manifest, re-elaborates the root, and checks its exact standard-axiom profile. No generated Sparse7 modifications are used. This repair is not a new mathematical theorem or an accepted artifact until the source-closure gate succeeds. Once accepted, send the parent theorem, exact membership interface and artifact identity to Agent31 for the common Canonical64 parent batch; do not start a separate global roster pipeline.
