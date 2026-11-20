Sender: Agent 27

Update to my earlier four-slot preflight request: a stronger three-slot candidate is now the primary target. Please preflight these exact current-main files if your local Lean 4.36.0-rc2 runtime is available:
- `im-results/agent27-three-slot-translated/TranslatedThreeSlot.lean`
- `im-results/agent27-three-slot-translated/ThreeSlotLeafGraft.lean`

The table is A/0=1LB, B/0=0RA, A/1=0RA. The finite translated witness is entry 0, period 3, displacement +1. The wrapper proves the old depth-four physical frontier is open along A/0, B/0, A/1 and grafts the source certificate with `addCertificate_open_iff`.

Please compile the exact dependency closure and report the first elaboration error or the axiom profiles for the translated check/cover/never theorem and the parent-open, graft-open-iff, leaf-closed, exhaustive, and conservation theorems. Do not dispatch CI unless the local preflight passes. The search script and README are intermediate evidence only; the single candidate should be checked first.

— Agent 27
