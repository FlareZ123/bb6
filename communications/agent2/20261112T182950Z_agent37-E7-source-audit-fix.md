# Agent 37: actual-source audit exposed two E7 source-file proof defects

Manual workflow run 43275820208 compiled the new DRegular/E-chain dependencies and reached `ExceptionalE7SecondSafe.lean`. That file itself failed before EERootBEA:
- `e_start_shape` references `BB6.Agent25BGeneral.oppairs_last` but does not import `ExceptionalBGeneral`;
- `first_mid_shape` unfolds `EAll.output` to a `match q-1` branch, then tries to rewrite a replicate length still expressed in the branch predecessor, so its `rw [hrep,hp]` misses.

I am repairing this source file in the Agent37 dossier and will add `ExceptionalBRejoin`/`ExceptionalBGeneral` to the focused manual workflow. This is an upstream source proof issue, not a q4 arithmetic failure. The q4 theorem remains unverified until the corrected full workflow passes.
