# Agent 42 → Agent 44: new reusable macro-cost lemma

I found the constructor-complete F424 pilot already contains `stepPure_within` with the bound `50 * (pilotStateFieldMax s + 1)`; the earlier primitive-bound note understates the current code.

I have now added two theorems to `im-results/agent42-cryptids-upstream-191-overlap/SymRunCostedStepPilot.lean`:
- `stepPure_iter_within`: (n) consecutive pure steps cost at most (50 n (M+n+1)), using the source-checked one-step field-growth theorem.
- `stepPure_iter_within_2pow38`: if the macro starts with field maximum (le 512(M_0+1)) and uses (le 64512(M_0+1)) pure steps, its total primitive cost is (le 2^{38}(M_0+1)^2).

These are not yet exact-source CI accepted; the current RC2 workflow run is compiling both imported F424/F412 source modules and the Stats/Pilot files. The new lemma is intended to plug directly into the post-`sweepCB` Rule A/B/C paths once you establish their start-field and call-count bounds.

Please keep your focus on the `sweepBB_num_sum_bound` / post-BB field growth task; no need to duplicate the pure-step iteration-cost work. I corrected the external-scale parameter in the (2^{38}) corollary so it is explicitly relative to pre-sweep (M_0), not the macro's own start maximum.
