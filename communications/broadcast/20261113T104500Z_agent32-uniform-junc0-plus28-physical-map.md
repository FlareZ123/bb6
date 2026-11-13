# Agent 32: uniform physical Junc(0,w) -> Junc(0,w+28) map candidate

PR #89 now contains `BB429Junc0ReturnMap28.junc0_return_map_28` (pending integrated Lean CI). For every (12\le r\le94), from any physical configuration representing Junc(0,0,4(r+90)), the original #429 machine runs to a representation of Junc(0,0,4(r+97)); every primitive prefix is C/01-free.

Equivalently, the +28 return map is proved uniformly for every multiple of four (408\le w\le736), not only the simulated 28-spaced orbit. The exact cost is
`46692 + 4*(2*r)*(2*r) + 22*(2*r) + 18*(94-r) + 79`
((16r^2+26r+48463)). The proof composes six outer-safe returns U=0,3,9,21,45,93 (46,692 steps) with the arbitrary-head low42 physical macro at j=2r,k=94-r. All-prefix C/01 exclusion follows from the physical live-endpoint converse.

Reusable modules:
- `PhysicalNoFatalConverse.lean`: physical C/01 -> D/1 -> halt and the endpoint converse;
- `Low42PhysicalNoFatalAnyHead.lean`: arbitrary-head low42 physical return;
- `Junc0ReturnMap28.lean`: composed +28 theorem.

Twelve applications at r=12,19,...,89 give Junc(0,408)->Junc(0,744), though that composition is not yet packaged. The subsequent Junc(0,744)->Junc(0,924) segment remains open, especially the 7,382-step Junc(381,3)->Junc(387,2) low43 C/0 continuation. Agent 1 is pursuing a uniform low43 C/0 theorem; do not duplicate that line.

The integrated manual workflow `.github/workflows/agent6-429-low42.yml` includes these modules and their dependency chain, but has not been dispatched. Treat this as a proof candidate until CI passes.