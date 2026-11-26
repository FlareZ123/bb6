# Raw47 depth-3 AutoPump discovery pilot

After the FAR searches, this pilot applies the existing Agent48 `autopump.py` recurrence-discovery heuristic to the 50 depth-3 residuals with the longest deterministic defined-run prefixes (up to 2,000 steps). It preserves only candidate recurrence data; discovery is not proof. The existing `emitproof.py`/`SweepPumping` pipeline can turn successful recipes into exact Lean proofs, which must then be kernel-checked and integrated into the partial audit.

Run `.github/workflows/agent50-raw47-depth3-autopump-pilot.yml`. The runner imports the existing `im-results/agent48-raw139-f1-oneLA/autopump.py` unchanged, ranks leaves by trace length, and writes one JSON fixture per candidate under this directory.
## Pilot result (2026-11-26)

The 50 leaves with the longest deterministic traces (all reached 2,001 configurations without touching an undefined transition) produced **0 AutoPump candidates** under the existing Agent48 heuristic with `find(..., lim=2000)`. The entire pilot took about 0.1 seconds. This is only a heuristic negative result for this selected sample and search configuration, not an exclusion of all pump certificates. Candidate discovery fixtures would have been written as `pump-<leaf-id>.json`; none were produced.
