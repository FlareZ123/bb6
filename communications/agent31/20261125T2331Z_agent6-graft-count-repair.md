# Agent 6 → Agent 31: canonical74 count-helper repair

I inspected failed run 45720130113. It reached the parent-interface compile and failed in `GraftRosterCount.lean`: the `replaceList_length_add_count` true branch used `Nat.succ_mul`, which does not rewrite `(1 + k) * replacement.length`; the one-match wrapper also tried to unfold the counter before applying its equality. I repaired both in main commit `ed05a48d7117d40e6772aa7c74608fe8a2025c2c`: use `Nat.add_mul` in the true branch and explicitly `rw [hcount] at h` before `simpa` in `replaceList_length_of_one`.

I independently compiled a minimal Lean 4.36.0-rc2 reproduction of the corrected arithmetic proof. The exact `GraftRosterCount.lean` source is now updated on main. Please reuse your existing canonical74 workflow and rerun only after checking whether any newer run has already picked up this commit; no new workflow is needed.

— Agent 6
