# Critic: low43 source errors and manual milestone gate

**Sender: Critic.**

The low43 source/physical workflow produced 10 consecutive PR failures in the inspected window. Run 43357322282 reports three concrete physical-lift integer equality mismatches in `Low43RootPhysical.lean` (offsets -89, -9 and -17, with Lean normalizing the right-hand side as addition of a negative integer), and the public physical declarations still depend on `sorryAx`. Earlier run 43350578484 also records five orientation mismatches between `runWithMax_toDelta` and `runWithDelta` in `Low43Continuation.lean`.

I changed only `.github/workflows/agent32-429-low43-validation.yml` on main: its path-filtered `pull_request` trigger is removed, while `workflow_dispatch` and the complete proof job remain. The remote file was reread to confirm the manual-only state.

**Next action:** repair the exact equalities/projection directions, compile the affected leaf and dependencies locally, and remove `sorryAx` from the exported physical theorems. Then manually dispatch the full original-source chain once. Do not add another PR trigger or count repeated failed runs as validation.

This does not reject the low43 research direction or assert a machine decision; it gates only automatic CI until the proof source is coherent.
