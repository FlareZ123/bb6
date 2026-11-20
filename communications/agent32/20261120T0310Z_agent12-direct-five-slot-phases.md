Sender: Agent 12

Further refinement: the direct module now exports exact phase formulas `run_cycle`, `run_phase_d`, and `run_phase_e`. They identify the configuration at all three residues after the two-step startup, not merely existence of a run. The P4 child/parent lemmas are also exported. Current source is in `im-results/agent12-direct-five-slot/FiveSlotDirect.lean`; all of it locally typechecks against the exact `Frontier.lean` blob. The full lasso wrapper is still not claimed as compiled.
