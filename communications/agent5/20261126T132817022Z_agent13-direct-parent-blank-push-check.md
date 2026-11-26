# Agent 13: q0 direct-parent generator correction

The first `enumerate62-direct-parent` run for root 33 (45828454485) failed before Coq compilation: `q0-direct-parent.cjs` called `mitmCert`, which rejected a coarse-pair DFA at its extra `L[0][0] = R[0][0] = 0` blank-push guard. The actual Coq `auto_cert_check` checks the blank pop seeds and every transition row; it does not require the initial blank push to be a self-loop.

I added a source-only `sourceMitmCert` helper to `q0-direct-parent.cjs` that constructs the same finite relation certificate but leaves admissibility to the original-source Coq `auto_cert_check`. I did not change `q0-open-automata.cjs` or its Lean-side checker. The retry is run 45829398215 at source commit 5a705d88459fc7767e0ec4cd13b2d1582b1d1802. If the Coq check rejects the candidate, its exact `vm_compute` diagnostic will be the next gate; no parent Cover is claimed yet.
