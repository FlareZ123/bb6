# Raw139 E0=1RE: complete candidate partition, symbolic growth proof

Parent [7,24,11,24,14,24,24,16,19,11,24,24], normalized depth-two E0=1RE. Ordinary code 4*destination+2*write+right; 24 is an unassigned transition. Initial exact first-query partition (250 steps, 120-step cycle lookback, FAR up to two DFA states): 15,548 splits, 357,605 ordinary leaves (257,197 cycles, 58,915 last-hole queries, 38,735 FAR, 2,758 open). Local partition SHA-256 ecf63ad9b138576ada33c90a02f21743b0ed8d7f6e401e3b959f62ac9cf10542.

Extended block-FAR and late-query search gives 2,660 block certificates, 79 finite queries, 18 cycles and one hard leaf (1873). Two finite queries have multiple holes: each has 24 ordinary children, with 36 block certificates and 12 finite last-hole queries total. Final 357,651 leaves: 257,215 translated cycles, 59,004 finite last-hole queries, 38,735 FAR, 2,696 block-FAR and one symbolic nonhalting leaf. The candidate uniform weighted bound is 19,745 (largest first query 19,739). All explicit halt alternatives are covered by the existing Hybrid first-query theorem in the proposed assembly.

## New symbolic hard-leaf theorem

Table 1873: [7,21,11,17,14,3,2,16,19,11,24,12] = 1RB0RF_1RC0RE_1LD1RA_1LA0LE_1RE1RC_---0LD. F0 is never queried. Let G(a,r,c) be state F, scanned symbol 1, left side nearest-first 0 1^a followed by 0 1^c when c>0, right side 1^r, with implicit zero tails. At blank step 35, G(4,2,0).

Exact macros:
- a>=1, r>=5: G(a,r,c) -> G(a+3,r-4,c+1) in 4a+8 steps.
- a>=2: G(a,1,c) -> G(c+5,a-2,0) in 7a+16 steps.
- a>=1: G(a,2,c) -> G(c+5,a+1,0) in 7a+28 steps.

For every k>=0 the macros give the positive-cost three-stage recurrence
G(4+2k,2+8k,0) -> G(5+2k,5+8k,0) -> G(6+2k,6+8k,0) -> G(4+2(k+1),2+8(k+1),0).
The stages use 2k, 2k+1, 2k+1 repetitions of the long macro, respectively. Thus the authentic blank orbit survives arbitrarily many ordinary steps. Lean 4.36.0-rc2 checks `BB6.Agent6E0OneRE1873.growth` and `never` with only [propext, Quot.sound], importing the accepted PartialAudit dependency closure from artifact 15121390168. Exact table transport into the Hybrid checker also passed locally, with standard axioms. No padding/trim approximation is used.

Four first queries at times 1434, 1007, 5819, 19739 pass via the zipper checker in `OneRELongQueries.lean`, with standard axioms. Direct raw kernel evaluation of the longest query exceeded a 30s local timeout, so these use `certifiedZip` and kernel decide.

## Acceptance status

Reproducer, generator and composer tracked here. Source-connected sharded parent audit run [45846437127](https://github.com/FlareZ123/bb6/actions/runs/45846437127), pinned source 5b160a000f2b21286f3a0f7fcabd92d13d8e4469, variant oneRE in the existing agent6-raw139-e0-zerorc.yml workflow. It was queued at 15:10:41Z. Do not claim parent closure or global reduction until the exact `BB6.Agent6E0OneRE.weighted` parent theorem is accepted.

E0=0RC independent audit [45827711630](https://github.com/FlareZ123/bb6/actions/runs/45827711630): 20/24 branch artifacts accepted; shards 00,07,12,18 were terminated by runner shutdown (exit 143), no proof error in final logs. Attempt 2 reruns only failed jobs and parent composition. No new 0RC search needed.
