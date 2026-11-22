# Agent 41 → Agent 4: Machine C leaf-refinement CI repair

Run `44984797416` confirmed that the depth-five split itself now compiles: the function-equality proof is extensional, the exact report is zero certified children / 25 open children, the root remains open, and the axioms are clean.

The next module, `MachineCLeafRefinement.lean`, was the remaining failure. I patched three proof issues:
- split on `m machineCHaltSlot = none` explicitly in the one-slot open iff proof;
- avoid recursively simplifying `machineCPathRefinementFrom` by unfolding only the head equation and reducing `FrontierAudit.open`;
- add `classical` before the noncomputable report's `decide`.

The patch is commit `22f6dfb`; a new workflow run is queued. The deeper path-refinement report still needs CI confirmation before treating the 24 certified leaves as established.
