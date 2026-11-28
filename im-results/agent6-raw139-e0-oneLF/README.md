# Raw139 E0=1LF: exact root-cover recovery

Parent `[7,24,11,24,14,24,24,16,22,11,24,24]`, first F0 query at t=8. The candidate bound is 90794; the required parent theorem is `BB6.Agent6E0OneLF.weighted : Cover (WeightedBound 90794) parent`. It is not yet accepted.

## Current exact proof frontier

Original source-connected parent run [45942475346](https://github.com/FlareZ123/bb6/actions/runs/45942475346) compiled its shared closure (608 modules) and **23 of 24** ordinary root Covers. Roots 01–23 succeeded. Root00 alone was canceled at its 90-minute job limit while compiling OLFBlock00_0095; the preceding leaf theorems H752–H759 printed standard axioms. No rejection of a Lean proof was reported in the retrieved terminal log. The unuploaded partial root00 objects cannot be treated as accepted artifacts.

Core/source artifact 15173635308 (40705561 bytes; SHA-256 aa673e0f56981cab70c945740449b16fece64b1be044fed3d26a0b6221b624fc) contains the unchanged generated source partition. Recovery [46093526398](https://github.com/FlareZ123/bb6/actions/runs/46093526398) uses the existing manual workflow with variant oneLF, recovery_run_id 45942475346, and recovery scheduler source 6688b77b673e54772a0ffc1598a66ec25a2eed5a. It derives the exact original revision from core.json, partitions only the root00 dependency DAG into independent automata and tree cuts, merges source-checked objects with consistent identities, checks the original root00 theorem, and invokes the original compose.py with the 23 old successful artifacts. No new census, table substitutions, or modified mathematical proof terms. Local shell and Python calls returned ClientError before execution in this invocation; this targeted CI is the executable diagnostic. Recovery remains pending; the scheduler itself has not yet been runtime-tested.

## Mathematical certificates and exhaustive partition

Original full oneLFSearch run 45932206380 (artifact summary 15169460132) reproduced the 18046 initial open leaves and processed each exact ID once. Its witness classes were 17774 block, 472 last, 55 cycle, 3 sparse n-gram and 18 residual descendants (12 additional splits). Initial partition 944772 leaves (41077*23+1); final expanded partition 945048 leaves (41089*23+1). The observed weighted maximum 90794 becomes a universal parent bound only when all exact Covers and their parent composition are checked.

All 18 exceptional tables have source-connected kernel-checked Cover (WeightedBound 90794) certificates through OneLFExceptionalAudit.lean, with only [propext, Classical.choice, Quot.sound]: ten translated-cycle Covers and eight NeverHalts certificates, each literal checked by tableOK_sound. The costly H1352 width-five proof uses the accepted sparse certificate (artifact 15171375225). Seven source-connected exceptional artifacts share 596 distinct modules with no conflicting identities. merge_exceptional.py pins archive SHA-256, proof revision, root and workflow run; lean_compile_closure validates the actual import graph and source identities.

AlternatingSweep.lean checks three compact sweep growth certificates for F0=0LA, F1=0LC, A1=0RA, C1=0LA, D0 absent, B1=0LE/0RF/1LD (run 45932501839); these were already candidate-classified by BlockFAR and do not subtract from the 18 holdouts. The earlier parent run 45934352918 failed on an off-by-one leaf count before compilation; the corrected partition has the above 945048 leaves.

## Acceptance boundary

No complete OneLF parent, normalized-row removal, global roster subtraction, or BB(6) verdict is claimed. Once accepted, use the exact literal and bound to discharge the matching E0=1LF obligation in Agent14's current normalized Raw139 interface; the whole Raw139 Cover and global consumer remain separate obligations.
