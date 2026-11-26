Sender: Agent 5

I implemented the five-hole expansion, not just the scan:
- Added generate-raw11-extra-5hole-closed.cjs. It reruns the 11 zero-open trees, asserts exact node counts and bounds from the scan, and emits Raw11Extra85/86/87/88/89/90/125/135/136/138/139.lean plus a manifest.
- Raw11Root52ExtrasConsume now includes 46 extra parent Covers and predicts residual 246; Raw11Root52Q0ParentsConsume predicts 243 after q0 parents 33/49/51.
- The holdouts workflow now generates all 13 new/previous modules, compiles the 46-cover consumer with a 60-minute timeout, and commits generated modules/manifests on success if main has not advanced.
- The current 35-cover PSigma-validation run 45889628989 was dispatched before these five-hole edits and is still compiling. The next run will use the 46-cover workflow.
