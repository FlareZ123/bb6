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

## Acceptance status and remaining proof edge

The original source-connected sharded audit [45846437127](https://github.com/FlareZ123/bb6/actions/runs/45846437127) (source 5b160a000f2b21286f3a0f7fcabd92d13d8e4469) produced 23 accepted exact root artifacts; only root00 was cancelled. The complete parent remains unaccepted.

Root00's largest certificate H60 has table [7,3,11,21,14,0,12,16,19,11,24,9] (F0 free). Its previous block-FAR4 certificate contains 564 control rows and 1543 automaton states. A symmetric width-18 sparse n-gram fixed point needs only **2159 abstract configurations**, with twelve state/symbol row counts [165,120,68,76,369,143,16,441,202,483,0,76]. It contains the authentic blank start, and every listed state's outgoing transition is defined and closed under the allowed left/right tail edges. The F0 row is empty. The new [emit60.py](emit60.py) uses the existing Agent47 sparse checker to generate twelve independently checked rows and the exact same `BB6.Agent6E0OneREBlocks.H60.ctr` and `never` interface. Local Lean 4.36.0-rc2 accepted the complete theorem with [propext, Classical.choice, Quot.sound]; generated data and all twelve row checks took approximately 22 seconds in total, largest observed process peak about 2.13 GB. Dependencies were taken from accepted oneRE core artifact 15130259578 and Raw111 sparse artifact 15001870656. This is a local replacement proof, not acceptance of the full root or parent.

The existing manual E0 audit now supports a oneRE recovery mode: use recovery_run_id=45846437127, variant=oneRE and source_sha identifying the replacement generator. It downloads the old core and exact generated sources, checks only root00 after replacing H60, then composes the old 23 roots with the repaired root. Source checkout remains pinned to the original 5b160a revision; the replacement generator revision and modified generated module hashes are retained in the recovery artifacts. The existing strict source/olean dependency validation remains in force. No accepted sibling is re-enumerated.

The independent zeroRF parent is now source accepted in [45880300288](https://github.com/FlareZ123/bb6/actions/runs/45880300288); its result is recorded in the zeroRF dossier. The zeroRC audit still has four missing roots (00,07,12,18).
