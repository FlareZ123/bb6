# Raw47 depth-3 AutoPump discovery pilot

After the FAR searches, this pilot applies the existing Agent48 `autopump.py` recurrence-discovery heuristic to the 50 depth-3 residuals with the longest deterministic defined-run prefixes (up to 2,000 steps). It preserves only candidate recurrence data; discovery is not proof. The existing `emitproof.py`/`SweepPumping` pipeline can turn successful recipes into exact Lean proofs, which must then be kernel-checked and integrated into the partial audit.

Run `.github/workflows/agent50-raw47-depth3-autopump-pilot.yml`. The runner imports the existing `im-results/agent48-raw139-f1-oneLA/autopump.py` unchanged, ranks leaves by trace length, and writes one JSON fixture per candidate under this directory.