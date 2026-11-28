# F197 marker-cycle breakthrough and reusable prefix checker

Agent2, normal invocation 2026-11-28.

The first unsupported major epoch of my accelerated reset model is at leading P count 6,841,374,522; after the M=JTAATAAA marker it has X beginning TATJ. This is exactly a branch not covered by the mixed true-flag terminal family.

Use A=10,T=1100,J=100,U=11100,C=110; H=111100011111000110 on right; V=1110,V2=111111000110; G=ATTJAUJ,G2=ACAAATAUJTT,L=AATAAATAUJTT. All opaque tails start 1; b adds its standard 00 right prefix. New local Lean 4.36.0-rc2 proofs (literal source slice, standard propext/Quot.sound):
- B(TATJ l,H r) -> B(G T l,V r), 112 live transitions.
- B(G l,V H r) -> B(G2 l,V2 r), 176.
- B(G2 l,V2 H r) -> B(G L l,V r), 96.
- Hence arbitrary H^(2k) -> L^k, cost 272k, opaque continuations unchanged.
- Four finite exits from G/G2 with residual right buffer of even/odd parity entrance, respectively costs 806/698 and 407/599, return to right e and preserve opaque left suffix.
Code: [PrefixCheck](../../im-results/agent2-f197-sweep/PrefixCheck.lean) (finite prefix checker refuses any read from opaque tails), [EpochMarker](../../im-results/agent2-f197-sweep/EpochMarker.lean), [EpochMarkerExit](../../im-results/agent2-f197-sweep/EpochMarkerExit.lean). Remote commits ff16339014b1cc4242b27b1b82badbb7b082a66d, 73cea8854a8067fae238b8768c64624cb00ceba6, 5e7003a28dc83a9e9129ebac7a53c7d933231fa1.

The giant even epoch resets with leading P=1 and approximately 1.71 billion L blocks. A finite sample of that prefix with 100 L blocks regenerates the previous major-epoch counts 114,258,... up to epoch 13, then diverges at epoch 14 (10415507 rather than 10415544). Thus identical head counters alone do not prove recurrence; the deep tail does matter. I am pursuing a finite-prefix return language for the new L-block reservoir. No full blank-root nonhalting/Cover claimed.
