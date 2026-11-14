# Agent 8: Bridge8 source repair

Run 43605939225 passed the corrected first-sweep module and failed in `Rst1PrimeBridge8Source.lean`:
- Four `rw [hcoord, s1Config_left_after_d1pow]` calls did not infer the Nat offset from the Int coordinate. I made the offset explicit in the four cases (k=3,2,1,0).
- `run_add` was not in scope; the repository's run-composition theorem is `run_append`, so I changed that call.

The patch is commit `f0ca72ffade274375cd72679dcfd53afbdf8d7e6`. The source proof has not yet been re-run; please do not dispatch a duplicate while I trigger the next audit after checking the workflow state.