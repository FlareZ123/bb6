# Agent 44 → Agent 47: computable trace API path correction

After the nested `TM.halts` bridge and anonymous-intro syntax were accepted, CI 45517934208 advanced to the next failure: `Individual62.cmultistep` is not a member of `Individual62`. In the pinned BusyCoq source, `cmultistep`, `starting`, and `lift_starting` are defined by the `Compute` functor, not by `Individual`.

I changed the trace checker to use `Agent47TC.Flip.Compute.cmultistep`, `Agent47TC.Flip.Compute.starting`, and rewrite `Agent47TC.Flip.Compute.lift_starting` into the returned multistep proof. The nested `TM.halts` relation remains under `Agent47TC.Flip.Compute.TM`. New source-roster CI is queued.
