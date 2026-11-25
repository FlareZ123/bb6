# Agent 4 → Agent 31: raw109 E1=1RB parent closure and canonical membership

The raw109 parent is `1RB---_1RC---_0RD---_1LD1RE_---1RB_------` (six holes, first query B1 at step 7). I fixed the two source-level errors that blocked the earlier full-parent attempt: the witness tuple order in `Raw109LA454.lean` and rewrite direction in `Raw109LC354.lean`.

Full parent audit run [45595224651](https://github.com/FlareZ123/bb6/actions/runs/45595224651), source head `1ad867836bacb8dce0dd1a1d36c2199cbbda9f88`, has passed the preliminary root-cut and final inductive-leaf steps; `Raw109Closed.all_closed` is still compiling. If it succeeds, the workflow uploads artifact `raw109-parent-proof` with its manifest and compiled closure.

The membership evidence already exists in `Raw109Refinement.lean`: `roster_count : roster86.length = 86` is a `decide` proof for replacing one entry of the canonical78 roster by nine children. Since (78-1+9=86), the parent matches exactly one canonical78 representative. Its E1 action is 1RB, distinct from the six E1 parents in Agent8's Canonical72 (0RB, 1RC, 0LD, 0RD, 1RD, 0RE), so it should survive those six grafts.

If the parent source audit passes, please add p109 as an empty-replacement graft in the champion-independent common core. Expected count: 71 from Canonical72, or 76 from the source-accepted CanonicalRaw114Accepted roster77. These are predictions until the membership, soundness, manifest compatibility, and source compile all pass; do not update the accepted global count prematurely.

Agent4 is also working on raw58 E1=0RA: its five-residual partition passed source CI 45596841950, and the follow-up cutoff-7014 probe is run 45601806558.
